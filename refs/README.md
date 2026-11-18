# Sources

| key | source | stored here |
|---|---|---|
| **HA2010** | Y. Zhang, P. L. Jones, R. Jetley, *A hazard analysis for a generic insulin infusion pump*, J. Diabetes Sci. Technol. 4(2):263–283, 2010. PMID [20307387](https://pubmed.ncbi.nlm.nih.gov/20307387/), [PMC2864162](https://pmc.ncbi.nlm.nih.gov/articles/PMC2864162/), doi:10.1177/193229681000400207 | `HA2010-PMC2864162.txt` (text of the PMC full-text page) |
| **SR2011** | Y. Zhang, R. Jetley, P. L. Jones, A. Ray, *Generic safety requirements for developing safe insulin pump software*, J. Diabetes Sci. Technol. 5(6):1403–1419, 2011. PMID [22226258](https://pubmed.ncbi.nlm.nih.gov/22226258/), [PMC3262707](https://pmc.ncbi.nlm.nih.gov/articles/PMC3262707/), doi:10.1177/193229681100500612 | `SR2011-PMC3262707.txt` (text of the PMC full-text page) |
| **CFR862** | 21 CFR 862.1356, Interoperable automated glycemic controller ([eCFR](https://www.ecfr.gov/current/title-21/chapter-I/subchapter-H/part-862/subpart-B/section-862.1356)) | `21CFR-862.1356.txt` |
| **CFR880** | 21 CFR 880.5730, Alternate controller enabled infusion pump ([eCFR](https://www.ecfr.gov/current/title-21/chapter-I/subchapter-H/part-880/subpart-F/section-880.5730)) | `21CFR-880.5730.txt` |

The two CFR sections were downloaded on 2026-11-18 from the eCFR versioner API (edition
2026-01-01) and converted to plain text. US federal regulations are in the public domain.

The two journal articles are free to read on PubMed Central. The PDFs could not be
downloaded by a script (PMC serves them behind a browser JavaScript check), so the
stored copies are the plain text of the PMC full-text HTML pages, fetched 2026-11-18.
Note: PMC's metadata marks both articles `pmc-prop-open-access: no` (free to read, but
not under an open licence). Check the licence before publishing these copies.

Every HA2010/SR2011 ID cited in `docs/REQUIREMENTS.md` and `docs/TRACEABILITY.md` was
checked against these texts on 2026-11-18 (all exist; SR2011 1.3.5 and 1.3.16 are cited
as adaptations, see REQUIREMENTS). The IDs refer to:

- HA2010 Table 1 (hazardous situations: 1.1 overdose, 1.2 underdose), Table 2
  (operational causes, e.g. 2.14 unexpected delivery of insulin), Table 3 (software
  causes: 3.1.2 incorrect correction bolus, including "calculator uses obsolete BG
  readings"; 3.1.3 inappropriate or incorrect calculation of IOB), Table 4 (hardware
  causes: 4.6.1–4.6.3 clock and synchronisation errors).
- SR2011 Table 1 (requirements on insulin administration: 1.2.1 basal increments,
  1.2.5 temporary basal rate and duration limits, 1.3.1 maximum bolus, 1.3.5 no bolus
  while another is in progress, 1.3.11 duration of insulin activity, 1.3.12 age of
  the BG reading used, 1.3.14 no correction when BG is below target, 1.3.16 unabsorbed
  insulin, 1.7.1 no reverse flow, 1.8.2 no delivery while suspended).
