import ErdosProblems.ArgumentGraph.Derived.Erdos68
import ErdosProblems.ArgumentGraph.Derived.Erdos243
import ErdosProblems.ArgumentGraph.Derived.Erdos249
import ErdosProblems.ArgumentGraph.Derived.Erdos251
import ErdosProblems.ArgumentGraph.Derived.Erdos257
import ErdosProblems.ArgumentGraph.Derived.Erdos269
import ErdosProblems.ArgumentGraph.Derived.Erdos1041
import ErdosProblems.ArgumentGraph.Derived.Erdos1049

-- Compiling this probe compiles the generated frontier modules (the probe build
-- builds the modules a probe imports); every derive command in them runs under
-- argumentGraph.strict.
#print axioms ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separation_parent.idle
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold.idle
