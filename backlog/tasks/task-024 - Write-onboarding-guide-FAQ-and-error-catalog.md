---
id: TASK-024
title: 'Write onboarding guide, FAQ, and error catalog'
status: To Do
assignee: []
created_date: '2026-03-03 02:46'
updated_date: '2026-03-03 02:58'
labels:
  - docs
  - dx
dependencies:
  - TASK-001
  - TASK-002
references:
  - SESSION.md
  - docs/src/SUMMARY.md
priority: low
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
DX audit identified three documentation gaps:

1. **No adoption guide**: Docs explain each feature but there's no "Adding Tix to an existing project" walkthrough. No "Common patterns and how to annotate them."
2. **No FAQ**: "Why is my type `?`?" is the most common question every persona will ask. No troubleshooting section.
3. **No error catalog**: What does each diagnostic mean, what causes it, how to fix it.

These are the primary user-facing documentation gaps for adoption.
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 docs/src/ contains an adoption/onboarding guide with step-by-step instructions
- [ ] #2 FAQ page answering common questions (especially 'why is my type ?')
- [ ] #3 Error catalog documenting each diagnostic with cause and fix
- [ ] #4 SUMMARY.md updated with new pages
<!-- AC:END -->

## Definition of Done
<!-- DOD:BEGIN -->
- [ ] #1 tests + lints pass
- [ ] #2 Documentation updated
- [ ] #3 No test regressions
- [ ] #4 Feature has test coverage
<!-- DOD:END -->
