Require Import Coqlib Integers List.
Require Import Registers Globalenvs Op.

(* Safety of operations and instructions. *)

Definition condition_is_safe (c: condition): bool := match c with
  | Ccomp _ | Ccompu _ | Ccompimm _ _ | Ccompuimm _ _ => Archi.ptr64
  | Ccompl _ | Ccomplu _ | Ccomplimm _ _ | Ccompluimm _ _ => negb Archi.ptr64
  | _ => true
end.

Definition condition_safe (c: condition): Prop := condition_is_safe c = true.

Definition op_is_safe (op: operation): bool := match op with
  | Odiv | Odivu | Odivl | Odivlu | Omod | Omodu | Omodl | Omodlu => false
  | Ointoffloat | Ofloatofint | Ointofsingle | Osingleofint | Olongoffloat | Ofloatoflong | Olongofsingle | Osingleoflong => false
  | Oindirectsymbol _ => false
  | Oshl | Oshr | Oshru => false
  | Oshrimm x | Oshruimm x | Oshlimm x => Int.ltu x Int.iwordsize
  | Oshrximm _ | Oshrxlimm _ | Oshldimm _ => false
  | Olea _ => false
  | Oleal (Aindexed _) => Archi.ptr64 | Oleal (Ainstack _) => true | Oleal _ => false
  (* 64-bit is forbidden because Vptr and Vlong both have type Tlong (in 64-bit), how unfortunate *)
  (* Actually this should depend on Archi.ptr64. If Archi.ptr64, all long operations are forbidden, else all int operations. lol *)
  | Olowlong | Ohighlong | Onegl | Oaddlimm _ | Omull | Omullimm _ | Omullhs | Omullhu | Oandl | Oandlimm _ | Oorl | Osubl
  | Oorlimm _ | Oxorl | Oxorlimm _ | Onotl | Oshll | Oshllimm _ | Oshrl | Oshrlimm _ | Oshrlu | Oshrluimm _ | Ororlimm _ => false
  | Ocmp c | Osel c _ => condition_is_safe c
  | _ => true
end.

Definition op_safe (op: operation): Prop := op_is_safe op = true.
