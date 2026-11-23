# Safety standards for insulin pumps and AID controllers

Status: survey, written 2026-11-20. It extends section 2 of `docs/timing-plan.md`,
which lists the sources that the project already checked. This file adds the
standards that the timing plan marked "not checked", the FDA guidance documents, the
clinical consensus definitions and the academic formalizations. The catalog of
properties that this survey produces is `docs/mtl-catalog.md`.

AID (automated insulin delivery) means a CGM, a controller such as oref0 and a pump in
a closed loop.

## How to read the confidence labels

Short keys such as SR2011 or CFR862 refer to the references in section 10, which also
give the links.

Most standards in this file are paywalled. The project does not hold their text. Each
entry has one of three labels:

- read: a person or agent read the text on a primary source page,
- secondary: the content comes from a named secondary source, a publisher preview or a
  search excerpt of the primary document,
- unconfirmed: the sources disagree, or the content comes from memory.

Do not cite a clause number marked secondary or unconfirmed in `docs/REQUIREMENTS.md`
until a person reads the clause. The research for this file did not use copies of
standards that the copyright holder did not publish.

## 1. Summary

The sources examined here give no fixed numeric timing limit for an AID controller.
This does not mean that timing is unregulated. The regulations (21 CFR 862.1356,
880.5730) and the closed-loop standard (IEC 60601-1-10) require the maker to specify,
disclose and test timing values. The paywalled standards were not read in full, so a
fixed limit in a clause not seen here remains possible. The numbers that exist
come from three places:

1. test methods for pumps, for example the trumpet-curve windows of IEC 60601-2-24,
2. disclosure thresholds, for example the 10 s alarm delay of IEC 60601-1-8,
3. clinical consensus definitions of glucose events, for example "at least 15
   consecutive minutes below 54 mg/dL".

oref0 itself fixes the numbers that the project proves: a reading whose reported age,
rounded to 0.1 minute, is above 12 minutes is stale (catalog A1),
30 to 120 minutes for a temp basal, the SMB interval, and the duration of insulin
action (DIA).

## 2. Regulations

| source | scope | access | time-related content | confidence |
|---|---|---|---|---|
| 21 CFR 862.1356 (iAGC, interoperable automated glycemic controller) | the controller | public, `refs/` | if communication is interrupted, lost or re-established, therapy stays safe ((b)(1)(vi)). Safe operation on out-of-bounds data ((b)(3)(iv)). Record of critical events, including connectivity events ((b)(4)). No numbers | read |
| 21 CFR 880.5730 (ACE pump, alternate controller enabled pump) | the pump | public, `refs/` | measures that keep therapy safe when communication is interrupted, lost or re-established. Reverting to a pre-programmed safe rate is one example that the text gives ((b)(4)). The temp expiry of the catalog (B2, B3) is the project's adaptation. Detect occlusion "within a clinically relevant timeframe" ((b)(1)(ii)). Basal accuracy at time points such as 1, 6 and 12 h ((b)(7)(iv)). Longest time to occlusion alarm ((b)(7)(v)). No numbers | read |
| 21 CFR 862.1355 (iCGM, integrated CGM) | the sensor | public | accuracy bands (table below). Rate-of-change criteria. Real-time readings at "clinically meaningful time intervals" ((b)(2)). Consistent performance throughout the sensor wear period ((b)(1)(iv)). No clinically significant gaps in sensor data over the claimed sensor life ((b)(1)(vii)). The sensor cannot be used past its claimed wear period ((b)(5)). Labelling states frequency and duration of data gaps ((b)(7)) | read |
| EU MDR 2017/745, Annex I | all devices | public | 21.1: delivered amount set and kept accurately. 21.2: prevent accidental release of dangerous amounts. No numbers | secondary |

iCGM accuracy, 21 CFR 862.1355 (b)(1)(v)(A) to (G), for the adult population. The
lower one-sided 95% confidence bound on the share of readings within the band of the reference value.

| iCGM range | band | bound above |
|---|---|---|
| below 70 mg/dL | ±15 mg/dL | 85% |
| below 70 mg/dL | ±40 mg/dL | 98% |
| 70 to 180 mg/dL | ±15% | 70% |
| 70 to 180 mg/dL | ±40% | 99% |
| above 180 mg/dL | ±15% | 80% |
| above 180 mg/dL | ±40% | 99% |
| whole range | ±20% | 87% |

Two rate-of-change criteria follow ((b)(1)(v)(J) and (K)). At most 1% of readings may
show a rise faster than +1 mg/dL/min when the true rate is below −2 mg/dL/min. At most
1% may show a fall faster than −1 mg/dL/min when the true rate is above +2 mg/dL/min.
Criteria (H) and (I) forbid an iCGM value below 70 with a reference above 180, and the
reverse. Pediatric data, or a justification for their absence, are required by
(b)(1)(vi). These are
statistical claims about a sensor population. They are not temporal properties of one
run, but they can justify an assumption on the CGM input (catalog section D).

## 3. Product standards (IEC 60601 family)

### 3.1 IEC 60601-2-24:2012, infusion pumps and controllers

Edition 2.0 is current (EN 60601-2-24:2015 in Europe). An edition 3 project is at the
working draft stage, with a committee draft milestone in 2027. Paywalled.

Insulin pumps are not excluded. They fall under "infusion pump for ambulatory use",
and some clauses carve them out (secondary, from search excerpts of the SIS and ANSI webstore previews, no page
numbers). The 1998 edition
excluded disposable devices, which can matter for patch pumps (secondary).

Time-related content, all secondary:

- Trumpet curves. The maximum and minimum flow errors E_p(max) and E_p(min) are
  computed over observation windows P = 2, 5, 11, 19 and 31 minutes. Annex AA also
  lists P = 1 minute. For a pump with a longer sample interval S, the windows are
  S, 2S, 5S, 11S, 19S and 31S. The curves come from the second hour of the test and
  from the last hour of the administration set change interval. This agrees with the
  numbers that `docs/timing-plan.md` section 2.3 gave from memory.
- Occlusion. The instructions for use state the occlusion alarm threshold and the
  maximum time to activate the occlusion alarm, at several rates and thresholds. The
  standard defines the unintended bolus released after an occlusion clears and gives a
  method to measure it. The standard sets no limit for either value.
- Accuracy. The standard sets no pass or fail limit. Insulin pump makers usually
  claim ±5% (Ziegler et al. 2021, PMC8080918).

Insulin-specific test practice, not part of the standard (Freckmann et al. 2019,
PMC6477586, and Pleus et al. 2019, doi:10.1177/1932296818806509): trumpet windows of 15,
60, 150, 330, 570 and 930 minutes after 24 h of stabilization, and 1 h windows. In a
72 h test at 1.0 U/h, 7 of 10 systems had at least 95% of 1 h windows within ±15%.

### 3.2 IEC 60601-1-10:2007 + A1:2013 + A2:2020, physiologic closed-loop controllers

Consolidated edition 1.2. A second edition is in preparation. Paywalled. A PCLC
(physiologic closed-loop controller) adjusts therapy from a measured patient variable.
An AID system is one.

Definitions, secondary, from the
[iTeh preview of IEC 60601-1-10:2007](https://cdn.standards.iteh.ai/samples/44104/f54ef528536349c184901f98dd408bca/IEC-60601-1-10-2007.pdf):
response time in 3.24 and settling time in 3.25, printed page 13 (checked by the Codex
review of 2026-11-20). The consolidated 2020 edition was not seen:

- response time: time for the step response to reach a stated share of its final
  value,
- settling time: time from a step input until the output stays within a stated
  tolerance (5% is usual),
- overshoot: largest transient deviation from the final value,
- steady-state deviation: deviation from the target after transients end.

The standard sets no limits. The maker specifies these values and verifies them, and
considers disturbances, worst-case behaviour and latency in risk management
(secondary, Johner Institute). Amendment 2 added logging of PCLCS variables and
requires that a patient model used in validation is shown to be credible (secondary).

The FDA "Computation of PCLC Response Metrics" tool (read,
https://www.fda.gov/medical-devices/regulatory-science-tools-catalog/computation-physiologic-closed-loop-controller-response-metrics)
computes these metrics plus median performance error, wobble and percentage of time in
target.

### 3.3 IEC 60601-1-8 (alarms) and IEC 60601-1-11 (home use)

IEC 60601-1-8:2006 + A1:2012 + A2:2020. Definitions, secondary, from the Har-El terms page (a
third-party rendering of the standard):

- alarm condition delay: time from the triggering event to the moment the alarm system
  decides that an alarm condition exists,
- alarm signal generation delay: time from the onset of the alarm condition to the
  alarm signal,
- audio paused and alarm paused: states of limited duration,
- reminder signal: a periodic signal during an inactivation state,
- latching: the signal continues after the trigger ends, until the operator acts.

If the sum of the two maximum delays is above 10 s, the maker discloses their
statistics in the instructions for use (clause 6.4.1, secondary). This is a disclosure
rule, not a limit. Burst and flash timing for alarm priorities is secondary, from vendor application
notes (Texas Instruments SLOA273, Challenge Electronics), not from the standard. An example is an interburst interval of 2.5 to 15 s for high priority.

IEC 60601-1-11:2015 + A1:2020 (home healthcare): an alarm on switch-over to the
internal power source, and an alarm with "sufficient time" before the source is
exhausted. No minutes are given (secondary).

For IEC 60601-1:2005 + A1:2012 + A2:2020 (general), the search found no timing numbers
relevant here. The standard was not read.

## 4. Process standards

In these process standards, no fixed timing value was found. They require the maker to
identify, specify and verify hazards and requirements, which can include timing. They
are IEC 62304:2006 + A1:2015
(software life cycle, edition 2 forecast for 2028), ISO 14971:2019 (risk management),
IEC 62366-1 (usability), ISO 13485:2016 (quality management), IEC 81001-5-1 and AAMI
TIR57 (security), IEC 80001-1 (networks) and ANSI/AAMI/UL 2800-1 (interoperability). They govern how
a maker derives and verifies requirements, so they decide how a catalog such as
`docs/mtl-catalog.md` is used, not what it contains. Editions in this paragraph are
unconfirmed except IEC 62304.

IEEE 11073-10419 (insulin pump) and 11073-10425 (CGM) are data models. 10425 calls CGM
sampling "typically 5 minute" (secondary). DTSec (Diabetes Technology Society
cybersecurity standard, protection profile v2.0, 2017) requires authentication,
integrity and confidentiality of communication. The Codex review of 2026-11-20 found
no explicit replay requirement in it. The GlobalPlatform SESIP profile for DTSec, a
public review draft, names protection against replay of messages (secondary). Replay
protection is a freshness requirement without a time bound.

## 5. FDA guidance

| document | status | time-related content | confidence |
|---|---|---|---|
| Infusion Pumps Total Product Life Cycle | final, 2014 | submit time to occlusion alarm, flow accuracy, bolus after occlusion. No numbers | secondary |
| Technical Considerations for Medical Devices with Physiologic Closed-Loop Control Technology | final, 2023 | sensor latency, actuator start-up delay, fallback modes with entry and exit criteria, limits on amounts delivered over time, reversion to fallback on sensor fault. No numbers | secondary |
| Content of IDE and PMA Applications for Artificial Pancreas Device Systems | final, 2012 | reliable communication between components. No numbers found | secondary |

The 2-hour limit on threshold suspend is a feature of the MiniMed 530G (P120010), not
a guidance requirement (secondary).

## 6. Hazard analyses and generic requirement sets

| source | content | confidence |
|---|---|---|
| HA2010, SR2011 (Zhang, Jones, Jetley et al.) | hazards and requirements for a generic insulin pump. Timing values are parameters x, y, z. The timed requirements are listed in `docs/timing-plan.md` section 2.1 | read |
| Generic Infusion Pump hazard analysis (Arney et al., UPenn MS-CIS-08-31, 2009) | low battery alarms, alarm silencing. The values "15 min low battery, 5 min depleted" are unconfirmed | secondary |
| GPCA (generic PCA pump) requirements and UPPAAL model (Kim et al., EMSOFT 2011, doi:10.1145/2038642.2038667) | 97 requirements. Safety requirements written as UPPAAL queries over timed automata. Example: no bolus while the pump alarms. A follow-up cites "infusion should start within 500 ms" | secondary |
| Event-B timing for the Generic Insulin Infusion Pump (Springer 2012, doi:10.1007/978-3-642-32355-3_10) | timing refinement of the GIIP | secondary |
| Blauw et al. 2016, review of AP safety and design requirements (PMC5093196) | control update interval "on the order of 15 min". After a gap in glucose data of about 10 to 20 min (algorithm dependent), the algorithm stops computing control actions and changes safely to fallback therapy, which can continue a patient-specific basal. Control can be stopped for at least 15 min. Compression lows last 15 to 30 min. Insulin action can last up to 8 h, so the controller tracks IOB. These are recommendations | read |

Formal work on artificial pancreas properties, secondary (the formulas were not read):

- Cameron, Fainekos, Maahs, Sankaranarayanan, RV 2015, doi:10.1007/978-3-319-23820-3_1:
  runtime verification of an artificial pancreas.
- Sankaranarayanan et al., ACM SIGBED Review 14(2), 2017: S-TaLiRo falsification of a
  controller against STL (signal temporal logic) properties. The reported example
  "insulin shutoff whenever BG ≤ 90 mg/dL" was falsified.
- Kushner et al., ICCPS 2018, and Springer 2019, doi:10.1007/978-3-030-17297-8_4:
  models, devices and MTL/STL properties of AP systems.
- Survey of V&V of AP systems, ICSTW 2024 (Queen's University), lists UPPAAL and
  UPPAAL-SMC work.
- Cumulative-time STL applied to hypoglycaemia, arXiv 2504.10325.

## 7. Clinical consensus definitions

Battelino et al. 2019, Diabetes Care 42:1593, doi:10.2337/dci19-0028 (read):

| metric | type 1 and type 2 target | older or high-risk target |
|---|---|---|
| time in range 70 to 180 mg/dL | > 70% (> 16 h 48 min per day) | > 50% |
| time below 70 mg/dL | < 4% (< 1 h) | < 1% |
| time below 54 mg/dL | < 1% (< 15 min) | |
| time above 180 mg/dL | < 25% | |
| time above 250 mg/dL | < 5% | < 10% |

For sufficient data, 14 days need at least 70% of readings. A CGM episode lasts
at least 15 minutes.

Event definitions differ between the two consensus papers. Keep them apart.

Danne 2017 (read by the Codex review of 2026-11-20):

- a hypoglycaemia event starts after at least 15 consecutive minutes below 70 mg/dL
  (level 1) or 54 mg/dL (level 2),
- an event of either level ends after at least 15 consecutive minutes at or above
  70 mg/dL,
- prolonged hypoglycaemia: below 54 mg/dL for at least 120 consecutive minutes
  (secondary).

Battelino 2023 (unconfirmed: from search excerpts and trial protocols, not from the
paper):

- level 1 and level 2 hypoglycaemia: at least 15 consecutive minutes below 70 or
  54 mg/dL, ending after at least 15 consecutive minutes at or above the threshold,
- hyperglycaemia of level 1 or 2: at least 15 consecutive minutes in 181 to 250 or
  above 250 mg/dL,
- extended hyperglycaemia: at least 90 cumulative minutes above 250 mg/dL within 120
  minutes, ending after 15 minutes below 180 (unconfirmed).

These definitions are outcome properties of a glucose trace. They apply to simulation
runs (`docs/SIM.md`), not to the controller alone, and simulation is not clinical
evidence.

## 8. Kinds of timing requirement

| kind | examples | where in the catalog |
|---|---|---|
| bounded response | occlusion → alarm within T, alarm delays, failure → failsafe within x s | B |
| freshness (past bound) | no increase when the rounded reported age is above 12 min (oref0, catalog A1). Fallback after a data gap of 10 to 20 min (Blauw) | A, B |
| bounded duration and fallback | temp basal ends at its deadline, revert to basal on lost communication, suspend at most 2 h (530G) | B |
| spacing | no microbolus within the SMB interval of the last bolus | A |
| periodicity | CGM every 5 min, loop cycle, reminder signals | B, D |
| escalation | unacknowledged alarm becomes audible after x min | B |
| window sum or average | delivered insulin in any window, trumpet curves, 1 h basal accuracy | C |
| persistence (debounce) | 15 consecutive minutes below 54 mg/dL | E |
| cumulative time and proportion | 90 of 120 min above 250, time in range over 14 days | E |
| control performance | settling time, overshoot, steady-state deviation | E |
| lifetime | sensor wear period, warm-up | D |

## 9. Gaps

- The exact clause text of IEC 60601-2-24, IEC 60601-1-8 and IEC 60601-1-10.
- The text of the 2012 APDS and 2023 PCLC guidance documents (their PDFs could not be
  parsed during the research).
- The STL formulas in the Sankaranarayanan and Kushner papers.
- The 2023 extended-event definitions.

## 10. References

The tables use the short keys below. Links go to the publisher, PubMed Central, the
eCFR or the standards body. Paywalled standards link to their catalogue page where one
was found.

### Regulations and FDA documents

| key | reference |
|---|---|
| CFR862 | 21 CFR 862.1356, Interoperable automated glycemic controller. [eCFR](https://www.ecfr.gov/current/title-21/chapter-I/subchapter-H/part-862/subpart-B/section-862.1356). Text in `refs/21CFR-862.1356.txt` |
| CFR880 | 21 CFR 880.5730, Alternate controller enabled infusion pump. [eCFR](https://www.ecfr.gov/current/title-21/chapter-I/subchapter-H/part-880/subpart-F/section-880.5730). Text in `refs/21CFR-880.5730.txt` |
| iCGM | 21 CFR 862.1355, Integrated continuous glucose monitoring system. [LII text](https://www.law.cornell.edu/cfr/text/21/862.1355) |
| EU MDR | Regulation (EU) 2017/745 on medical devices, Annex I. [EUR-Lex](https://eur-lex.europa.eu/legal-content/EN/TXT/HTML/?uri=CELEX%3A02017R0745-20260719) |
| FDA TPLC 2014 | FDA, Infusion Pumps Total Product Life Cycle, guidance, 2014. [PDF](https://www.fda.gov/media/78369/download) |
| FDA PCLC 2023 | FDA, Technical Considerations for Medical Devices with Physiologic Closed-Loop Control Technology, guidance, 2023. [PDF](https://www.fda.gov/media/154994/download) |
| FDA APDS 2012 | FDA, The Content of Investigational Device Exemption and Premarket Approval Applications for Artificial Pancreas Device Systems, guidance, 2012. [PDF](https://www.fda.gov/media/80644/download) |
| FDA PCLC tool | FDA, Computation of Physiologic Closed-Loop Controller Response Metrics, regulatory science tool. [page](https://www.fda.gov/medical-devices/regulatory-science-tools-catalog/computation-physiologic-closed-loop-controller-response-metrics) |
| MiniMed 530G | FDA premarket approval P120010 (threshold suspend). Cited from secondary sources, not read |

### Standards

| key | reference |
|---|---|
| IEC 60601-2-24 | IEC 60601-2-24:2012, Medical electrical equipment, Part 2-24: Particular requirements for the basic safety and essential performance of infusion pumps and controllers. Paywalled. Commentary: [MEDTEQ](https://www.medteq.net/article/2018/9/21/iec-60601-2-24-infusion-pumps-whats-the-story) |
| IEC 60601-1 | IEC 60601-1:2005 + A1:2012 + A2:2020, Medical electrical equipment, Part 1: General requirements for basic safety and essential performance. Paywalled. Not read |
| IEC 60601-1-10 | IEC 60601-1-10:2007 + A1:2013 + A2:2020, Collateral standard: requirements for the development of physiologic closed-loop controllers. Paywalled. [IEC webstore](https://webstore.iec.ch/en/publication/67383). Commentary: [Johner Institute](https://blog.johner-institute.com/regulatory-affairs/closed-loop-systems/) |
| IEC 60601-1-8 | IEC 60601-1-8:2006 + A1:2012 + A2:2020, Collateral standard: alarm systems. Paywalled. Terms: [Har-El](https://standards.har-el.com/Projects/181701/60601-1-8/html/3-Terms-Definitions.htm) |
| IEC 60601-1-11 | IEC 60601-1-11:2015 + A1:2020, Collateral standard: home healthcare environment. Paywalled |
| IEEE 11073-10425 | IEEE 11073-10425, Device specialization: continuous glucose monitor. [IEEE](https://standards.ieee.org/ieee/11073-10425/7248/) |
| IEEE 11073-10419 | ISO/IEEE 11073-10419:2019, Device specialization: insulin pump. [ISO](https://www.iso.org/standard/76535.html) |
| DTSec | Diabetes Technology Society, DTSec Protection Profile v2.0, 25 November 2017. [PDF](https://www.diabetestechnology.org/dtsec/DTSec%20PP.pdf). Version 1.0 of May 2016 is a separate [PDF](https://www.diabetestechnology.org/dtsec-protection-profile-final.pdf) |
| DTSec SESIP | GlobalPlatform, SESIP Profile for DTSec, public review draft v0.0.0.9. [PDF](https://globalplatform.org/wp-content/uploads/2023/10/GPT_SESIP_Profile_DTSec_v0.0.0.9_PublicRvw.pdf) |

The process standards of section 4 (IEC 62304, ISO 14971, IEC 62366-1, ISO 13485,
IEC 81001-5-1, AAMI TIR57, IEC 80001-1, ANSI/AAMI/UL 2800-1) are cited by name only.

### The software under study

| key | reference |
|---|---|
| oref0 | OpenAPS oref0, release 0.7.1, commit `88cf032aa74ff25f69464a7d9cd601ee3940c0b3`, MIT licence. [GitHub](https://github.com/openaps/oref0). Pinned in `vendor/oref0` |

### Hazard analyses, requirement sets and formal work

| key | reference |
|---|---|
| HA2010 | Y. Zhang, P. L. Jones, R. Jetley. A hazard analysis for a generic insulin infusion pump. J. Diabetes Sci. Technol. 4(2):263–283, 2010. [PMC2864162](https://pmc.ncbi.nlm.nih.gov/articles/PMC2864162/), [doi:10.1177/193229681000400207](https://doi.org/10.1177/193229681000400207) |
| SR2011 | Y. Zhang, R. Jetley, P. L. Jones, A. Ray. Generic safety requirements for developing safe insulin pump software. J. Diabetes Sci. Technol. 5(6):1403–1419, 2011. [PMC3262707](https://pmc.ncbi.nlm.nih.gov/articles/PMC3262707/), [doi:10.1177/193229681100500612](https://doi.org/10.1177/193229681100500612) |
| GIP | D. Arney, R. Jetley, P. Jones, I. Lee, A. Ray, O. Sokolsky, Y. Zhang. Generic infusion pump hazard analysis and safety requirements, version 1.0. Technical report MS-CIS-08-31, University of Pennsylvania, 2009. [publication page](https://rtg.cis.upenn.edu/gip_pub.php3) (the host did not resolve during the Codex review of 2026-11-20) |
| GPCA | B. Kim, A. Ayoub, O. Sokolsky, I. Lee, P. Jones, Y. Zhang, R. Jetley. Safety-assured development of the GPCA infusion pump software. EMSOFT 2011, 155–164. [doi:10.1145/2038642.2038667](https://doi.org/10.1145/2038642.2038667) |
| Event-B GIIP | H. Xu, T. Maibaum. An Event-B approach to timing issues applied to the Generic Insulin Infusion Pump. FHIES 2011, LNCS, Springer, 2012. [doi:10.1007/978-3-642-32355-3_10](https://doi.org/10.1007/978-3-642-32355-3_10) |
| Blauw 2016 | H. Blauw, P. Keith-Hynes, R. Koops, J. H. DeVries. A review of safety and design requirements of the artificial pancreas. Ann. Biomed. Eng. 44:3158–3172, 2016. [PMC5093196](https://pmc.ncbi.nlm.nih.gov/articles/PMC5093196/), [doi:10.1007/s10439-016-1679-2](https://doi.org/10.1007/s10439-016-1679-2) |
| Cameron 2015 | F. Cameron, G. Fainekos, D. M. Maahs, S. Sankaranarayanan. Towards a verified artificial pancreas: challenges and solutions for runtime verification. RV 2015, LNCS 9333, 3–17. [doi:10.1007/978-3-319-23820-3_1](https://doi.org/10.1007/978-3-319-23820-3_1) |
| Sankaranarayanan 2017 | S. Sankaranarayanan, S. A. Kumar, F. Cameron, B. W. Bequette, G. Fainekos, D. M. Maahs. Model-based falsification of an artificial pancreas control system. ACM SIGBED Review 14(2), 2017 |
| Kushner 2018 | T. Kushner, D. Bortz, D. M. Maahs, S. Sankaranarayanan. A data-driven approach to artificial pancreas verification and synthesis. ICCPS 2018, 242–252 |
| Kushner 2019 | T. Kushner et al. Models, devices, properties, and verification of artificial pancreas systems. In: Automated Reasoning for Systems Biology and Medicine, Springer, 2019. [doi:10.1007/978-3-030-17297-8_4](https://doi.org/10.1007/978-3-030-17297-8_4) |
| ICSTW 2024 survey | B. Nazzal, M. H. Alalfi, J. R. Cordy. A survey on the verification and validation of artificial pancreas software systems. ICSTW 2024. [PDF](https://research.cs.queensu.ca/home/cordy/Papers/ICSTW24-Survey-VV-APS.pdf) |
| CT-STL | Cumulative-time signal temporal logic, applied to hypoglycaemia. [arXiv:2504.10325](https://arxiv.org/abs/2504.10325) |

### Pump accuracy studies

| key | reference |
|---|---|
| Freckmann 2019 | G. Freckmann et al. Diabetes Technol. Ther., 2019. [PMC6477586](https://pmc.ncbi.nlm.nih.gov/articles/PMC6477586/) |
| Pleus 2019 | S. Pleus et al. J. Diabetes Sci. Technol., 2019. [doi:10.1177/1932296818806509](https://doi.org/10.1177/1932296818806509) |
| Ziegler 2021 | R. Ziegler et al., 2021. [PMC8080918](https://pmc.ncbi.nlm.nih.gov/articles/PMC8080918/) |

### Clinical consensus

| key | reference |
|---|---|
| Battelino 2019 | T. Battelino et al. Clinical targets for continuous glucose monitoring data interpretation: recommendations from the international consensus on time in range. Diabetes Care 42(8):1593–1603, 2019. [PMC6973648](https://pmc.ncbi.nlm.nih.gov/articles/PMC6973648/), [doi:10.2337/dci19-0028](https://doi.org/10.2337/dci19-0028) |
| Danne 2017 | T. Danne et al. International consensus on use of continuous glucose monitoring. Diabetes Care 40(12):1631–1640, 2017. [doi:10.2337/dc17-1600](https://doi.org/10.2337/dc17-1600) |
| Battelino 2023 | T. Battelino et al. Continuous glucose monitoring and metrics for clinical trials: an international consensus statement. Lancet Diabetes Endocrinol. 11(1):42–57, 2023. [doi:10.1016/S2213-8587(22)00319-9](https://doi.org/10.1016/S2213-8587(22)00319-9) |

### Temporal logics

| key | reference |
|---|---|
| MTL | R. Koymans. Specifying real-time properties with metric temporal logic. Real-Time Systems 2(4):255–299, 1990 |
| STL | O. Maler, D. Ničković. Monitoring temporal properties of continuous signals. FORMATS/FTRTFT 2004, LNCS 3253 |
| AvSTL | T. Akazaki, I. Hasuo. Time robustness in MTL and expressivity in hybrid system falsification. CAV 2015, LNCS 9207 |

Titles and page ranges not given in section 6 were added from memory and are not
checked: Kushner 2018 title, Battelino 2023 title and pages, Danne 2017 title and pages,
and the three logic papers. The Codex review of 2026-11-20 matched the DOIs to the
intended works and confirmed the AvSTL volume. Some entries are incomplete: the authors
of CT-STL and the titles of the pump accuracy studies. Check them before citing outside this repository.
