// Keep GitHub issue handling separate from the source checker so both work offline in tests.
module.exports = async function updateIssue({ github, context }, report) {
  const marker = '<!-- randomdo-upstream-core-watch -->';
  const digest = `<!-- upstream-fingerprint:${report.fingerprint} -->`;
  const issues = await github.paginate(github.rest.issues.listForRepo, {
    ...context.repo, state: 'all', creator: 'github-actions[bot]', per_page: 100,
  });
  const issue = issues.find(i => !i.pull_request && i.body?.includes(marker));
  if (report.changes.length === 0) {
    if (issue?.state === 'open') {
      await github.rest.issues.update({ ...context.repo, issue_number: issue.number, state: 'closed' });
    }
    return;
  }
  if (issue?.state === 'open' && issue.body?.includes(digest)) return;

  const run = `${context.serverUrl}/${context.repo.owner}/${context.repo.repo}/actions/runs/${context.runId}`;
  const mappings = report.changes.map(c =>
    `- \`${c.local}\` → [\`${c.upstream}\`](https://github.com/leanprover/lean4/blob/${c.commit}/${c.path}#L${c.start}-L${c.end})`);
  const body = [marker, digest,
    'Lean core has changed in these tracked declarations since their recorded baselines:', '',
    ...mappings, '', `[Review the upstream diffs](${run}), then update the affected adaptations and baselines.`,
  ].join('\n');
  if (issue) {
    await github.rest.issues.update({ ...context.repo, issue_number: issue.number, body, state: 'open' });
  } else {
    await github.rest.issues.create({
      ...context.repo, title: 'Lean core changes affecting adapted definitions', body,
    });
  }
};
