Require Import Memory Values.

(* For simplicity, we assume the definedness of memory reads via an axiom.
   The correct, but very heavy solution would be to specialize def_regset (which assert that no regs are Vundef)
   with a set of "super-public" registers that may be Vundef.
   Those super-public registers are never used in any unsafe operations.
   Then, Iloads and other unsafe (i.e. possibly returning Vundef) operations can exist,
   but only in uniform positions and when all their uses and defs are super-public.
   For now, we haven't implemented this as mem-loads are only an example
   for how to use the uni-chain theorem in Predication, laying the focus on the uniform positions
   but not on the definedness. *)
Axiom mem_load_always_defined: forall chunk m a v, Mem.loadv chunk m a = Some v -> v <> Vundef.