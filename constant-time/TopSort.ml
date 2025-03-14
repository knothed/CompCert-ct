open Graph
open List
open Datatypes

let rec to_int = function
| O -> 0
| S x -> (to_int x) + 1;;

let remove_all_edges_from: coq_G -> nat -> coq_G = fun g v ->
   { vs = g.vs; es = filter (fun (src,dst) -> not (src=v)) g.es }

let nodes_without_pred: coq_G -> nat list = fun g ->
   List.filter (fun v -> predecessors g v = []) g.vs

let remove_vertices: coq_G -> nat list -> coq_G = fun g vs ->
   { vs = List.filter (fun v -> not (List.mem v vs)) g.vs; es = g.es }

let top_sort: coq_G -> nat list = fun g ->
   let rec sorting_loop g preds acc =
      match preds with
      | [] -> g, acc
      | pred :: preds ->
         let g' = remove_all_edges_from g pred in
         let isolated = nodes_without_pred g' in
         let g'' = remove_vertices g' isolated in
         sorting_loop g'' (List.append preds isolated) (List.append acc isolated)
   in
   let entries = nodes_without_pred g in
   let g' = remove_vertices g entries in
   let (g'', result) = sorting_loop g' entries [] in
   let result = List.append entries result in
   match g''.vs with
   | [] -> result
   | _ -> [] (* Graph has a cycle *)
