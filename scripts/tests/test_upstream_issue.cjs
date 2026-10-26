const assert = require('node:assert/strict');
const { test } = require('node:test');
const updateIssue = require('../upstream-issue.cjs');

const context = {
  repo: { owner: 'example', repo: 'RandomDo' }, serverUrl: 'https://github.com', runId: 42,
};
const report = {
  fingerprint: 'abc',
  changes: [{ local: 'RDo.randOps', upstream: 'Lean.Elab.Do.DoOps.default',
    commit: 'deadbeef', path: 'src/Lean/Elab/Do/Basic.lean', start: 10, end: 20 }],
};
const marker = '<!-- randomdo-upstream-core-watch -->';
const issue = { number: 7, state: 'open', body: marker };

async function run(issues, current = report) {
  const calls = [];
  const github = {
    paginate: async () => issues,
    rest: { issues: {
      listForRepo: {},
      create: async args => calls.push({ operation: 'create', ...args }),
      update: async args => calls.push({ operation: 'update', ...args }),
    } },
  };
  await updateIssue({ github, context }, current);
  return calls;
}

test('creates one issue containing mappings and a link to the complete report', async () => {
  const [call] = await run([]);
  assert.equal(call.operation, 'create');
  assert.equal(call.owner, context.repo.owner);
  assert.equal(call.repo, context.repo.repo);
  assert.match(call.body, /RDo\.randOps/);
  assert.match(call.body, /blob\/deadbeef\/src\/Lean\/Elab\/Do\/Basic\.lean#L10-L20/);
  assert.match(call.body, /https:\/\/github.com\/example\/RandomDo\/actions\/runs\/42/);
});

test('updates an existing tracker and ignores other issues and pull requests', async () => {
  const calls = await run([{ number: 1, body: 'Unrelated issue' },
    { number: 2, body: marker, pull_request: {} }, issue]);
  assert.equal(calls.length, 1);
  assert.equal(calls[0].operation, 'update');
  assert.equal(calls[0].issue_number, 7);
});

test('does not update an issue when the relevant edits are unchanged', async () => {
  const [created] = await run([]);
  assert.deepEqual(await run([{ ...issue, body: created.body }]), []);
});

test('closes the tracker when no differences remain', async () => {
  const calls = await run([issue], { ...report, changes: [] });
  assert.deepEqual(calls, [{ operation: 'update', ...context.repo, issue_number: 7, state: 'closed' }]);
  assert.deepEqual(await run([], { ...report, changes: [] }), []);
  assert.deepEqual(await run([{ ...issue, state: 'closed' }], { ...report, changes: [] }), []);
});

test('reopens the same issue when differences remain', async () => {
  const [created] = await run([]);
  const [call] = await run([{ ...issue, state: 'closed', body: created.body }]);
  assert.equal(call.operation, 'update');
  assert.equal(call.issue_number, 7);
  assert.equal(call.state, 'open');
});

test('propagates API failures', async () => {
  const github = { rest: { issues: {} }, paginate: async () => { throw new Error('API unavailable'); } };
  await assert.rejects(updateIssue({ github, context }, report), /API unavailable/);
});
