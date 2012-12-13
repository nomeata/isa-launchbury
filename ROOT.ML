no_document use_thys ["~~/src/HOL/Library/FuncSet"];

quick_and_dirty := true;
Toplevel.skip_proofs := true;
Goal.parallel_proofs := 0;

use_thys ["Correctness","CorrectnessUpd"];
