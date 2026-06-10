# Lean-Community: wie ich die Formalisierung einbringe

*Strategie- und Arbeitsnotiz, Stand 2026-06-02. Ergänzt `contacts.md` (dort:
Endorsement-/Prior-Art-Kontakte). Code-Stellen beziehen sich auf
`Lean/CutAndProject/CutAndProject/Basic.lean` (2862 Z.) und `…/Irrational.lean`
(896 Z.).*

## TL;DR — der konkrete Plan

- Das *Theorem* gilt unter Experten als Folklore → der Wert liegt in der
  **Formalisierung**, nicht im Resultat.
- Im Lean-Code steckt ein **allgemeiner, wiederverwendbarer Kern** (elementare
  Zahlentheorie: Verteilung von `N` aufeinanderfolgenden Resten mod `D`), der
  besser in **Mathlib** aufgehoben wäre als nur im eigenen Repo.
- Ein erster Mathlib-Abgleich findet diese Kapselung **nicht** in Mathlib → echter
  Beitragskandidat. Die Dichte-/Irrationalitäts-Bausteine sind dagegen schon da.
- **Erster Schritt:** Lean Zulip — kurze Vorstellung in `#new members`, dann die
  konkrete „is there code for X?"-Frage. Entwürfe unten.

## Hintergrund — warum dieser Pivot

Zwei unabhängige Experten (Alan Haynes, Henna Koivusalo) bewerten den rationalen
Cut-and-Project-Fall als **„gelöst" / Folklore** — das Theorem gilt nicht als
publikationswürdig neu (Korrektheit ist nicht das Problem, Neuheit schon). Beide
haben jedoch unaufgefordert angemerkt, dass die **Lean-Formalisierung neu sein
könnte**.

→ Konsequenz: das Theorem nicht weiter Zahlentheorie-Journals als „neues Resultat"
anbieten. Was weitergetragen wird, ist die **Formalisierung — an die Lean-/
Formal-Methods-Community**, nicht an Zahlentheoretiker (die Lean nicht nutzen und
das Artefakt gar nicht beurteilen können).

## Der entscheidende Reframe

> **Nicht:** „Ich habe ein neues Theorem bewiesen, bitte anerkennen."
> **Sondern:** „Ich habe X formalisiert — ist das nützlich, gibt es das schon in
> Mathlib, was habe ich übersehen?"

Die Community reagiert auf Neugier und Beiträge, nicht auf Credentialing.

---

## Analyse des eigenen Lean-Codes

Dreigeteilt: (1) allgemein/wiederverwendbar = Mathlib-Kandidaten, (2) schon in
Mathlib vorhanden, (3) anwendungsspezifisch (bleibt im Repo).

### (1) Allgemein & wiederverwendbar — Mathlib-Kandidaten

**Tier A — stärkster Kandidat: Verteilung von `N` aufeinanderfolgenden Resten mod `D`**
(reine Zahlentheorie/Kombinatorik, keine Cut-and-Project-Semantik). Section
`ResidueDistribution`, `Basic.lean:54–332`.

| Deklaration | Zeile | Aussage |
|---|---|---|
| `count_hits` | 62 | Def.: `#{ i ∈ range N | (r0+i) ≡ x [ZMOD D] }` |
| `count_hits_add` / `_mul_D` / `_eq` | 116/127/134 | Additivität, volle Perioden, Division-mit-Rest-Zerlegung |
| `sum_count_hits` | 100 | `∑ₓ count_hits = N` |
| `residue_distribution` | 140 | **Kernsatz:** jede Klasse wird `⌊N/D⌋` oder `⌈N/D⌉` mal getroffen; genau `N % D` Klassen „schwer" |
| `uniform_residue_distribution` | 231 | `D ∣ N` ⇒ jede Klasse genau `N/D` mal |
| `non_uniform_…_of_not_dvd` | 211 | `D ∤ N` ⇒ echt nicht-uniform |
| `count_hits_unit`, `…_eq_count_hits`, `residue_distribution_unit` | 248/257/287 | Multiplikation der Reste mit einer Einheit `u ∈ (ZMod D)ˣ` permutiert nur die Klassen → Verteilung invariant |

**Tier B — sauber, aber spezieller** (Section `Minimality`, `Basic.lean:334–491`):

| Deklaration | Zeile | Aussage |
|---|---|---|
| `cyclic_interval` | 336 | Def.: `s` aufeinanderfolgende Reste mod `D` |
| `heavy_set_is_cyclic_interval` | 379 | die „schweren" Klassen bilden ein zusammenhängendes zyklisches Intervall |
| `cyclic_interval_stabilizer_trivial` | 464 | ein echtes, nichtleeres zyklisches Intervall (`0<s<D`) hat **trivialen Translations-Stabilisator** |
| `right_boundary_exists` / `_unique` | 418/443 | Rand eines zyklischen Intervalls |

### (2) Schon in Mathlib — **nicht** neu erfinden (Code nutzt es bereits)

| Thema | Mathlib | wo im Code |
|---|---|---|
| Kronecker-Dichte `ℤ + aℤ` (irrational) | `dense_addSubgroupClosure_pair_iff`, `irrational_neg_iff` | `Irrational.lean:75` `dense_internal_image` ist nur ein Wrapper |
| Injektivität `x+a·y` für irrationales `a` | `Irrational`-API + Casts | `Irrational.lean:43` `tildeP_injective` |
| Einheiten aus Teilerfremdheit | `ZMod.unitOfCoprime` | `Basic.lean:34–38` `alpha_unit`/`beta_unit` |
| Faserweises Zählen | `Finset.card_eq_sum_card_fiberwise` | `sum_count_hits`, `residue_distribution` |
| **Minimalperiode** | `Function.minimalPeriod` existiert, ist aber **iterations-basiert** (`f:α→α`) — **kein** Treffer für die additive Folgen-Periode. Additive Variante: `Function.Periodic f c := ∀x, f(x+c)=f x` | `IsPeriod`/`HasPeriodLength` (`Basic.lean:498/501`) |

**Konsequenz für (2):** `IsPeriod` ließe sich über `Function.Periodic` ausdrücken
(kleine Vereinfachung, kein Beitrag). Eine *minimale* additive Periode ist in
Mathlib nicht fertig gekapselt, aber trivial. `coprime_alpha_D`/`coprime_beta_D`/
`D_pos` (`Basic.lean:11/20/26`) sind Einzeiler aus `Nat.Coprime`-API → zu trivial
für einen Beitrag.

### (3) Anwendungsspezifisch — bleibt im Repo

Alles mit Cut-and-Project-Semantik: ab `GeometricProjection` (`Basic.lean:512`) die
gesamte Maschinerie — `cumulative_hits`, `V`, `sorted_multiset`,
`difference_sequence`, alle `…_unit`- und `set_…`-Varianten, `c_r`, sowie die
Hauptsätze `main_theorem*` / `set_main_theorem*` (Z. 1903, 1982, 2274, 2411, 2490,
2562, 2815, 2849) und die Perioden-/`sigma_`-Lemmas. In `Irrational.lean` die
Geometrie (`tildeP`, `sInternal`, `W`, `acceptedSet`, `enumerate`, `ell`, `gap`)
und das Aperiodizitäts-Argument (`period_lifts_to_lattice_translation:704`,
`lattice_translation_must_be_zero:798`, `prop_irrational:879`).

---

## Mathlib-Abgleich (Stand 2026-06-02)

**Methode:** Mathlib4-Doku-Suche + Loogle (`loogle.lean-lang.org`) + Code-Inspektion.
**Befund:**

- **Tier-A-Kernsatz (`residue_distribution`)** — *keine* fertige Mathlib-Kapselung
  gefunden (weder per Konzeptsuche noch per Loogle-Konstantensuche). Die *Bausteine*
  (`Finset.card_eq_sum_card_fiberwise`, `ZMod`-API, `Nat.div_add_mod'`) sind da, das
  *Resultat* offenbar nicht. → **bester Beitragskandidat.** *(Mittel-hohe Sicherheit;
  Definitivklärung gehört in `#Is there code for X?`.)*
- **Tier B (zyklisches Intervall, trivialer Stabilisator)** — vermutlich nicht in
  Mathlib, aber nischig; ggf. als Begleit-Lemmas zu Tier A.
- **Kronecker-Dichte / Irrationalität** — **vorhanden** (Code verwendet sie direkt).
- **Minimalperiode (additiv)** — nicht gekapselt; `Function.minimalPeriod` ist
  iterationsbasiert.

---

## Wege, nach Priorität

### 1. Lean Zulip — der zentrale Ort (erster Schritt)

`https://leanprover.zulipchat.com` — offen, kostenlos anmelden. Streams:
**#new members** (Vorstellung), **#Is there code for X?** (gibt es Lemma Y schon?),
**#mathlib4** (Entwicklung).

**Entwurf — `#new members` (Englisch, so wie dort üblich):**

> Hi all! I'm Dirk Kunert, an independent researcher with a mechanical-engineering
> background (not a professional mathematician). I just finished my first sizeable
> Lean 4 + Mathlib project: a ~3,700-line formalization of the minimal gap-period of
> one-dimensional rational cut-and-project sequences, including the rational/irrational
> dichotomy — no `sorry`, `axiom`, or `admit`. Repo: https://github.com/dkunert/cut-and-project
>
> The underlying theorem turns out to be folklore in the aperiodic-order community
> (two experts kindly confirmed), so my interest now is the formalization itself. Part
> of it is general number theory that might belong in Mathlib rather than my project —
> e.g. the distribution of `N` consecutive integers across residue classes mod `D`
> (each class hit `⌊N/D⌋` or `⌈N/D⌉` times). I'd love to learn whether such pieces
> already exist and whether they'd be welcome as contributions. Pointers to docs/etiquette
> I should read first are very welcome — thanks!

**Entwurf — `#Is there code for X?` (die konkrete Frage):**

> Is there existing Mathlib API for the distribution of `N` consecutive integers across
> residue classes mod `D`? Concretely, for `c x := (Finset.range N).filter (fun i =>
> (r0 + i : ZMod D) = x) |>.card`, the facts that every `c x ∈ {N/D, N/D + 1}`, that
> exactly `N % D` classes attain the larger value, and that all are equal iff `D ∣ N`.
> I have this proved (via `Finset.card_eq_sum_card_fiberwise`) but want to avoid
> reinventing a wheel. Thanks!

### 2. Mathlib — „Publikation" mit echter Anerkennung

`https://github.com/leanprover-community/mathlib4` — verdienstbasiert, **kein
Endorsement-Gatekeeping, nur Review**. Will *allgemeine, wiederverwendbare* Resultate
→ die komplette Formel ist zu speziell, aber **Tier A** (ggf. + Tier B) ist ein
realistischer Kandidat. Ablauf: erst auf Zulip „wäre das willkommen?" → CLA → Contribution-
Guide auf `leanprover-community.github.io` → klein anfangen (Tier A zuerst).

### 3. Writeup / Konferenz (optional, später)

- **Blogpost zuerst** — günstigster Weg, eine Formalisierung sichtbar zu machen.
- **Kurzpaper** bei **CPP** (mit POPL) oder **ITP** — nur bei echter
  „Formalisierungs-Geschichte". Für ein 1-D-Folklore-Resultat eher grenzwertig als
  eigenständiges Paper.
- ⚠️ **Archive of Formal Proofs (AFP)** ist **nur Isabelle**, nicht Lean — fällt weg.

## Was „Erfolg" realistisch heißt

Kein Paukenschlag, sondern: ein paar allgemeine Lemmas (Tier A) in Mathlib,
wohlwollendes Feedback, ein sauberer öffentlicher Artefakt — und falls arXiv weiter
gewünscht, ein Endorser aus **cs.LO / math.LO** statt Zahlentheorie. Freundliche, aber
knappe Reaktionen erwarten.

## Konkrete nächste Schritte (Checkliste)

- [x] Lean-Code durchgesehen, allgemein vs. anwendungsspezifisch getrennt (s. o.).
- [x] Erster Mathlib-Abgleich (Tier A offenbar nicht vorhanden).
- [x] Zulip-Entwürfe vorbereitet (oben).
- [ ] Zulip-Account anlegen.
- [ ] Repo aufräumen: README, das die Formalisierung erklärt (was; wie geprüft: 0
      `sorry`/`axiom`/`admit`, Lean-/Mathlib-Version, Build-Anleitung).
- [ ] `#new members`-Vorstellung posten, dann `#Is there code for X?`-Frage.
- [ ] Je nach Resonanz: Tier A als erste kleine Mathlib-PR isolieren *oder* Blogpost.

## Links

- Lean Zulip: https://leanprover.zulipchat.com
- Lean-Community-Hub / Contribution-Guide: https://leanprover-community.github.io
- Mathlib4: https://github.com/leanprover-community/mathlib4
- Mathlib4-Doku: https://leanprover-community.github.io/mathlib4_docs
- Loogle (Typ-/Namenssuche): https://loogle.lean-lang.org · Moogle (semantisch): https://www.moogle.ai
- `Function.minimalPeriod` (iterationsbasiert): https://leanprover-community.github.io/mathlib4_docs/Mathlib/Dynamics/PeriodicPts/Defs.html
- `Function.Periodic` (additiv): https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Periodic.html
- Eigenes Repo: https://github.com/dkunert/cut-and-project (Tag `v1.4-arxiv`)
