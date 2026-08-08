#!/usr/bin/env python3
"""Prueft die Konsistenz der beiden Companion-Papiere.

`cut-and-project` und `three-gap-theorem-lean` zitieren einander.  Damit
entsteht ein Fehler, den keine Pruefung eines einzelnen Repositoriums finden
kann: Aendert das eine seinen Titel, so veraltet das Zitat im anderen -- und
in beiden sieht fuer sich genommen alles stimmig aus.  Genau das ist am
7. August 2026 passiert.

WAS HIER GEPRUEFT WIRD, UND WARUM GERADE DAS

Ein Zitat mit Versionsangabe verweist nicht auf den heutigen Stand des
Schwesterpapiers, sondern auf einen bestimmten Tag.  Die richtige Frage lautet
also nicht "stimmt der zitierte Titel mit dem heutigen ueberein", sondern
"stimmt er mit dem Titel ZUM GEPINNTEN TAG ueberein".  Dieses Skript
vergleicht deshalb gegen `git show <tag>:<datei>`.

Daraus folgt auch, dass "die gepinnte Version ist der neueste Tag" KEIN
sinnvolles Kriterium ist: Zitieren sich zwei Papiere wechselseitig mit
Versionspin, so ist diese Forderung unerfuellbar.  Jeder neue Tag in A macht
den Pin in B veraltet, dessen Korrektur einen neuen Tag in B verlangt, und so
fort.  Ein neuerer Tag wird darum nur als Hinweis gemeldet, nicht als Fehler.

Es braucht kein Netz: geprueft wird gegen die lokalen Git-Objekte.  Hinkt ein
Repositorium hinterher, hilft vorher `git fetch --tags`.

Aufruf:  ./check_companions.py [-v]
Rueckgabe: 0 = alles stimmig, 1 = mindestens ein Befund.
"""

import os
import re
import subprocess
import sys

# Jeder Eintrag beschreibt EIN Papier und das Zitat, mit dem es sein
# Schwesterpapier auffuehrt.  Neue Companion-Beziehungen hier eintragen.
PAPIERE = [
    {
        "name": "three-gap-theorem-lean",
        "tex": "paper/three_gap_theorem_lean.tex",
        "zitiert": "Kunert2026",
        "schwester": "cut-and-project",
    },
    {
        "name": "cut-and-project",
        "tex": "LaTeX/rational_cut_and_project_gap_periods.tex",
        "zitiert": "KunertThreeGap2026",
        "schwester": "three-gap-theorem-lean",
    },
]

TEXQUELLE = {p["name"]: p["tex"] for p in PAPIERE}

GRUEN, ROT, GELB, AUS = "\033[32m", "\033[31m", "\033[33m", "\033[0m"
if not sys.stdout.isatty():
    GRUEN = ROT = GELB = AUS = ""


def finde_wurzel(start):
    """Das Verzeichnis, das beide Repositorien enthaelt -- von hier aufwaerts."""
    p = os.path.abspath(start)
    while True:
        if all(os.path.isdir(os.path.join(p, r)) for r in TEXQUELLE):
            return p
        eltern = os.path.dirname(p)
        if eltern == p:
            raise SystemExit("Kein Verzeichnis gefunden, das %s enthaelt."
                             % " und ".join(TEXQUELLE))
        p = eltern


WURZEL = finde_wurzel(os.path.dirname(os.path.abspath(__file__)))


def git(repo, *argumente):
    return subprocess.run(
        ["git", "-C", os.path.join(WURZEL, repo), *argumente],
        capture_output=True, text=True,
    )


def lies_aus_baum(repo, pfad):
    """Dateiinhalt im Arbeitsbaum."""
    with open(os.path.join(WURZEL, repo, pfad), encoding="utf-8") as f:
        return f.read()


def lies_aus_tag(repo, tag, pfad):
    """Dateiinhalt zum Zeitpunkt eines Tags, oder None."""
    e = git(repo, "show", "%s:%s" % (tag, pfad))
    return e.stdout if e.returncode == 0 else None


def klammerinhalt(text, start):
    """Inhalt der bei `start` (Index der '{') beginnenden Gruppe."""
    tiefe = 0
    for i in range(start, len(text)):
        if text[i] == "{":
            tiefe += 1
        elif text[i] == "}":
            tiefe -= 1
            if tiefe == 0:
                return text[start + 1:i]
    raise ValueError("unbalancierte Klammer ab Position %d" % start)


def normal(s):
    """Vergleichsform: Tilde, Umbrueche und LaTeX-Kommentare raus."""
    s = s.replace("~", " ").replace("\\-", "")
    s = re.sub(r"%.*", "", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s.rstrip(",.").strip().lower()


def titel(texinhalt):
    m = re.search(r"\\title\s*(\[[^\]]*\])?\s*\{", texinhalt)
    if not m:
        return None
    return klammerinhalt(texinhalt, m.end() - 1)


def bibitem(texinhalt, schluessel):
    m = re.search(r"\\bibitem\{%s\}" % re.escape(schluessel), texinhalt)
    if not m:
        return None
    rest = texinhalt[m.end():]
    ende = re.search(r"\\bibitem\{|\\end\{thebibliography\}", rest)
    return rest[: ende.start()] if ende else rest


def zitat_titel(block):
    m = re.search(r"``(.*?)''", block, re.S)
    return m.group(1) if m else None


def zitat_version(block):
    m = re.search(r"version\s+\\texttt\{([^}]*)\}", block)
    return m.group(1) if m else None


def zitat_urls(block):
    return re.findall(r"\\url\{([^}]*)\}", block)


def tags(repo):
    return git(repo, "tag", "-l").stdout.split()


def versionsschluessel(tag):
    """Numerische Teile numerisch, damit v1.10 nach v1.9 kommt."""
    return [(1, int(t)) if t.isdigit() else (0, t)
            for t in re.split(r"(\d+)", tag) if t != ""]


def main():
    ausfuehrlich = "-v" in sys.argv or "--verbose" in sys.argv
    nummer = fehler = hinweise = 0

    def melde(ok, text, detail=""):
        nonlocal nummer, fehler
        nummer += 1
        marke = GRUEN + "OK  " + AUS if ok else ROT + "FEHL" + AUS
        print("%2d. [%s] %s" % (nummer, marke, text))
        if detail and (not ok or ausfuehrlich):
            for zeile in detail.splitlines():
                print("        " + zeile)
        if not ok:
            fehler += 1
        return ok

    def hinweis(text):
        nonlocal hinweise
        hinweise += 1
        print("    [" + GELB + "HINW" + AUS + "] " + text)

    print("Companion-Konsistenz  (Wurzel: %s)" % WURZEL)
    print("=" * 58)

    for p in PAPIERE:
        schwester, schluessel = p["schwester"], p["zitiert"]
        print("\n%s  zitiert  %s  als \\bibitem{%s}"
              % (p["name"], schwester, schluessel))

        block = bibitem(lies_aus_baum(p["name"], p["tex"]), schluessel)
        if not melde(block is not None, "Zitat ist vorhanden",
                     "\\bibitem{%s} fehlt in %s/%s" % (schluessel, p["name"], p["tex"])):
            continue

        version = zitat_version(block)
        vorhanden = tags(schwester)
        sortiert = sorted(vorhanden, key=versionsschluessel)
        if not melde(version is not None, "Eine Version ist gepinnt",
                     "kein 'version \\texttt{...}' im Zitat.\n"
                     "Tags des Schwesterrepositoriums: %s" % " ".join(sortiert)):
            continue

        if not melde(version in vorhanden,
                     "Gepinnte Version %s existiert im Schwesterrepositorium" % version,
                     "vorhandene Tags: %s\n"
                     "Fehlt der Tag nur lokal, hilft 'git fetch --tags'."
                     % " ".join(sortiert)):
            continue

        # Der eigentliche Punkt: Titel ZUM GEPINNTEN TAG, nicht zum HEAD.
        inhalt = lies_aus_tag(schwester, version, TEXQUELLE[schwester])
        soll = titel(inhalt) if inhalt else None
        ist = zitat_titel(block)
        melde(soll is not None and ist is not None and normal(ist) == normal(soll),
              "Titel stimmt mit dem Titel zum Tag %s ueberein" % version,
              "zitiert:      %s\nzum Tag %s: %s"
              % (normal(ist or "-"), version, normal(soll or "-")))

        melde(bool([u for u in zitat_urls(block) if schwester in u and version in u]),
              "URL nennt Repositorium und gepinnte Version",
              "gefundene URLs: %s" % (", ".join(zitat_urls(block)) or "keine"))

        # Hinweise, keine Fehler.
        neuester = sortiert[-1] if sortiert else None
        if neuester and version != neuester:
            hinweis("Es gibt einen neueren Tag: %s (gepinnt ist %s). Das ist "
                    "zulaessig -- ein Zitat darf auf eine aeltere Fassung "
                    "verweisen." % (neuester, version))
        kopf = titel(lies_aus_baum(schwester, TEXQUELLE[schwester]))
        if soll and kopf and normal(kopf) != normal(soll):
            hinweis("Der Titel im Arbeitsbaum des Schwesterpapiers weicht vom "
                    "Titel zum Tag ab. Beim naechsten Tag muss dieses Zitat "
                    "nachgezogen werden.")

    print("\n" + "=" * 58)
    if fehler == 0:
        print(GRUEN + "Alle %d Pruefungen bestanden." % nummer + AUS
              + ("  (%d Hinweis(e))" % hinweise if hinweise else ""))
    else:
        print(ROT + "%d von %d Pruefungen fehlgeschlagen." % (fehler, nummer) + AUS)
    return 1 if fehler else 0


if __name__ == "__main__":
    sys.exit(main())
