# Vorschläge zur Lean 4 Konfiguration für die arXiv-Publikation

Diese Datei enthält Vorschläge zur Verbesserung der Lean 4 Konfiguration (`lakefile.toml`) und zur Generierung einer lesbaren Dokumentation, um die Qualität und Zugänglichkeit der Code-Basis für die arXiv-Publikation zu maximieren.

## 1. Ergänzungen für `lakefile.toml`

Für ein öffentliches Repository, insbesondere im Rahmen einer wissenschaftlichen Publikation, sollten in der `lakefile.toml` wichtige Metadaten hinterlegt werden. Dies hilft Suchmaschinen, Lean-Paketmanagern und Nutzern, das Projekt besser einzuordnen.

**Aktuelle `lakefile.toml`:**
```toml
name = "CutAndProject"
version = "0.1.0"
keywords = ["math"]
defaultTargets = ["CutAndProject"]
```

**Vorgeschlagene `lakefile.toml`:**
Fügen Sie eine beschreibende Zusammenfassung (`description`), passendere Schlüsselwörter und eine Open-Source-Lizenz hinzu (z.B. MIT oder Apache-2.0).

```toml
name = "CutAndProject"
version = "0.1.0"
description = "Lean 4 formalization of the period length formula for 1D cut-and-project sequences"
keywords = ["math", "number-theory", "aperiodic-order", "formalization"]
license = "MIT"
defaultTargets = ["CutAndProject"]

[leanOptions]
pp.unicode.fun = true # pretty-prints `fun a ↦ b`
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.29.1"

[[lean_lib]]
name = "CutAndProject"
```

## 2. HTML-Dokumentation mit `doc-gen4`

Viele Mathematiker und Leser auf arXiv haben Lean 4 nicht lokal installiert. Um den verifizierten Code und die exzellent dokumentierten Kommentare (`/-- ... -/`) leicht zugänglich zu machen, ist die Bereitstellung einer webbasierten Dokumentation Gold wert.

Mit dem Standard-Tool **`doc-gen4`** kann aus dem Lean-Code automatisch eine wunderschöne, klickbare HTML-Dokumentation generiert werden.

### So binden Sie `doc-gen4` ein:

1. **Ergänzen Sie Ihre `lakefile.toml`** um folgendes Requirement:
   ```toml
   [[require]]
   name = "doc-gen4"
   scope = "leanprover"
   rev = "main"
   ```

2. **Aktualisieren Sie die Abhängigkeiten:**
   Führen Sie im Terminal innerhalb des `Lean/CutAndProject` Verzeichnisses aus:
   ```bash
   lake update doc-gen4
   ```

3. **Dokumentation generieren:**
   Kompilieren Sie das Projekt inklusive Dokumentation:
   ```bash
   lake build CutAndProject:docs
   ```

4. **Ergebnis:**
   Im Verzeichnis `build/doc` befindet sich nun eine fertige statische Webseite. Diese können Sie direkt im Browser öffnen oder kostenfrei über **GitHub Pages** bereitstellen. 

Einen Link zu dieser Webseite können Sie dann in der `README.md` und eventuell sogar im LaTeX-Paper (in *Section 6: Machine-Checked Formalisation*) als "Web-readable formalization documentation" zur Verfügung stellen.
