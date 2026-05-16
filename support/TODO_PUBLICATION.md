# Publication TODO

Tracking the path from the current arXiv-ready state to a published paper.

Status snapshot (2026-05-16):
- Paper: 17 pp., 0 errors, 4 external review rounds closed
- Lean: 3,760 lines across `Basic.lean` + `Irrational.lean`, 0 `sorry`, 0 warnings
- Bibliography pinned to git tag `v1.0-arxiv`

---

## 1. Final pre-submission checks

- [ ] Recompile `LaTeX/rational_cut_and_project_gap_periods.tex` from a clean state and confirm 0 errors / 0 undefined refs
- [ ] Spell-check the full PDF (abstract, intro, theorems, discussion)
- [ ] Verify every `\cite{...}` resolves and every bibliography entry is actually cited
- [ ] Verify all internal `\ref{...}` / `\eqref{...}` resolve
- [ ] Re-check Table 1 line-number pins against current `Lean/Basic.lean`
- [ ] Confirm `Lean/` still builds cleanly (0 `sorry`, 0 warnings) at the tagged commit
- [ ] Decide on author metadata: full name, affiliation, ORCID, contact email

## 2. arXiv submission

- [ ] Pick primary category (likely `math.NT`) and secondary categories (e.g. `math.CO`, `math.DS`)
- [ ] Choose license (CC BY 4.0 vs. arXiv non-exclusive)
- [ ] Prepare submission bundle: `.tex` source + `.bbl` (not raw `.bib`) + any figures
- [ ] Decide whether to attach Lean source as ancillary files or link to a GitHub release
- [ ] Tag the submission commit (e.g. `v1.0-arxiv-submitted`) and push the tag
- [ ] Upload, preview rendered PDF, fix any arXiv-side complaints
- [ ] Submit; record the resulting arXiv ID and date here

## 3. Post-arXiv

- [ ] Add arXiv link + ID to `README.md`
- [ ] Update Lean repo (if separate) with arXiv reference in its README
- [ ] Email Alan Haynes (held in memory pending Phase 2 of learning plan — reassess timing now that paper is public)
- [ ] Optional: announce on relevant mailing lists / personal channels

## 4. Journal submission (optional, decide after arXiv)

- [ ] Shortlist target journals
- [ ] Read author guidelines for the chosen target (format, length, style file)
- [ ] Prepare journal-formatted version on a separate branch
- [ ] Write cover letter
- [ ] Submit; track manuscript ID and review timeline

## 5. Ongoing

- [ ] Watch for arXiv comments / emails and triage
- [ ] Keep a changelog of post-submission revisions (v2, v3, ...) if anything substantive changes
