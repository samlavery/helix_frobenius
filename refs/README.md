# External references

Third-party documents kept locally because they are not reachable by ordinary search.

## `zeta23_paper.pdf`

Claude / Anthropic, *"More than two thirds of the zeros of the Riemann zeta function lie on the
critical line"*, 2026-08-10. 35 pp.

- **Not on arXiv.** A title search of the arXiv API returns zero entries.
- **Not in the Lean artifact repo** (`anthropics/zeta-23-lean`); its README links only the repo.
- Reached in two hops from <https://www.anthropic.com/research/riemann-zeta>.
- Retrieved 2026-08-11 from
  <https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf>
- `sha256 6792988e6cd0e17690621ce898abd5d534f98407741bc7cb14bbe7d07c77d72f`

`zeta23_paper.txt` is `pdftotext -layout` output, kept for grepping. Line numbers in that file
are what `O1_LOSSY_NOTE.md` §7 and the register cite. **Superscript exponents split onto the
preceding line** in extraction — `10⁻⁶` appears as a bare `10` with `−6` above it. Read the PDF
before concluding an exponent is absent.

Three companion documents exist at the same host and are *not* mirrored here: an informal note
(`23455459f8832d06bb175cc0f88d019aed962ef8.pdf`), a methodology write-up
(`d7f3ecf1d01392d887f8bc974ca187e2a121b1ed.pdf`), and process transcripts
(`8a0d1add3c637b858a9a181e98c40e9548c3f44f.pdf`).
