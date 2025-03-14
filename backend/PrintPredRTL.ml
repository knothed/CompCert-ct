(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         David Knothe, FZI Forschungszentrum Informatik              *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printers for PredRTL code *)

open Format
open! Camlcoq
open Maps
open AST
open PrintAST
open PredRTL
open Graph
open SharedTypes

(* Printing of PredRTL code *)

let reg pp r =
  fprintf pp "x%d" (P.to_int r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let print_instruction pp f (pc, i) =
  if TaintAnalysis.uni_dec (taint_f f) f.coq_TAINT_RES (Nat.of_int pc) then
      fprintf pp "%7d:  " pc
  else
      fprintf pp "~uni %2d:  " pc;

  match i with
  | Inop ->
      fprintf pp "nop\n"
  | Iop(op, args, res) ->
      fprintf pp "%a = %a\n"
         reg res (PrintOp.print_operation reg) (op, args)
  | Iload(chunk, addr, args, dst) ->
      fprintf pp "%a = %s[%a]\n"
         reg dst (name_of_chunk chunk) (PrintOp.print_addressing reg) (addr, args)
  | Icond(cond, args) ->
      fprintf pp "if (%a)\n"
        (PrintOp.print_condition reg) (cond, args)
  | Ireturn None ->
      fprintf pp "return\n"
  | Ireturn (Some arg) ->
      fprintf pp "return %a\n" reg arg
  | Isel(_, _, _, _, _) ->
      () (* Isel only exist at a later stage *)

let print_function pp id f =
  if f.taint_attr <> [] then fprintf pp "__attribute((tainted(%a)))\n" regs f.taint_attr;
  fprintf pp "%s(%a) {\n" (extern_atom id) regs f.params;
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> compare pc1 pc2)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc - 1, i))
        (PTree.elements f.code)) in
  List.iter (print_instruction pp f) instrs;

  fprintf pp "\nEntry: %d\nOrig. edges with new target:\n" (Nat.to_int f.entry);
  List.iter (fun (v,w) ->
    fprintf pp "%3d → (%2d, %d)\n" (Nat.to_int v) (Nat.to_int w) (Nat.to_int (f.detour v w))
  ) f.g_pred.es;

  fprintf pp "\nJust PredRTL edges:\n";
  let sorted_es = List.sort (fun (pc1, _) (pc2, _) -> compare (Nat.to_int pc1) (Nat.to_int pc2)) f.g.es in
  List.iter (fun (v,w) ->
    fprintf pp "%3d → %2d" (Nat.to_int v) (Nat.to_int w);
    if f.uniform_cond v then fprintf pp "\n" else fprintf pp " - tainted condition\n"
  ) sorted_es;


  fprintf pp "}\n\n"

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp (prog: PredRTL.program) =
  List.iter (print_globdef pp) prog.prog_defs

let destination : string option ref = ref None

let print_if passno prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out (f ^ "." ^ Z.to_string passno) in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc

let print_fun_if passno id func =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out (f ^ "." ^ Z.to_string passno ^ "." ^ extern_atom id) in
      print_function (formatter_of_out_channel oc) id func;
      close_out oc
      