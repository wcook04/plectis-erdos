# Build the exposition PDF.
#
# Preferred: tectonic (self-contained, fetches TeX packages on first run):
#     https://tectonic-typesetting.github.io
# Fallback: a standard TeX Live install (run pdflatex twice for the TOC/refs).

# The two long-form manuscripts, then the Erdős Problem Notes: one short,
# standalone note per problem in the ErdosProblems expansion library.  Every
# name here must appear exactly once in docs/publication_contract.json.
PAPERS = erdos249-257-main-paper claim-faithful-publication-systems-paper \
  erdos-249-binary-totient-series erdos-257-mersenne-support-subseries \
  erdos-243-reciprocal-tail-rigidity erdos-251-prime-gap-dyadic-series \
  erdos-269-three-prime-running-lcm erdos-1049-rational-base-lambert
NOTES = erdos-249-binary-totient-series erdos-257-mersenne-support-subseries \
  erdos-243-reciprocal-tail-rigidity erdos-251-prime-gap-dyadic-series \
  erdos-269-three-prime-running-lcm erdos-1049-rational-base-lambert
ALIASES = module-aliases.tex
PREAMBLE = problem-note-preamble.tex

.PHONY: all check clean sync-root

all: $(PAPERS:%=%.pdf) sync-root

# Every manuscript keeps a root copy so the published byte-parity chain
# (root PDF == GitHub main == hosted site) stays intact.  Which manuscript a
# reader is *routed* to is a README question, not a filesystem one: the joint
# monograph is no longer the front door, but removing its root copy would
# break the deploy gate that compares those bytes.
sync-root: $(PAPERS:%=%.pdf)
	@for paper in $(PAPERS); do \
	  cp "$$paper.pdf" "../$$paper.pdf"; \
	done

check: all
	python3 ../scripts/check_rendered_paper_boundary.py
	python3 ../scripts/check_problem_note_sources.py

# The notes share one preamble, so a change there rebuilds all of them.
$(NOTES:%=%.pdf): $(PREAMBLE)

$(ALIASES): $(PAPERS:%=%.tex) ../scripts/build_paper_module_aliases.py
	python3 ../scripts/build_paper_module_aliases.py

%.pdf: %.tex $(ALIASES)
	@if command -v tectonic >/dev/null 2>&1; then \
	  tectonic $< ; \
	else \
	  pdflatex $< && pdflatex $< ; \
	fi

clean:
	rm -f $(PAPERS:%=%.pdf) $(PAPERS:%=%.aux) $(PAPERS:%=%.log) \
	  $(PAPERS:%=%.out) $(PAPERS:%=%.toc)
