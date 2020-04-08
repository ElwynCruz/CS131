open List

(*  
subset: determine if a is a subset of b
approach: for each element in a, check if it exists in b
if we find an element that is not, return false
otherwise return true

*)

let rec subset a b =
  match a with
    | [] -> true
    | hd::tl -> (List.exists (fun t -> hd = t) b ) && (subset tl b);; (*and with recursive calls returns 0 if any recursive call returns 0 *)

(*
equal_sets: returns true if the sets represented by a and b are equal
approach: if a is a subset of b and b is a subset of a, they represent equal sets
*)

let equal_sets a b =
  subset a b && subset b a;;

(*
set_union: returns a list that represents the set created by the union of sets a and b
approach: appending lists a and b creates a list that represents a set containing all the elements from a and b (the union). duplicates don't matter since it still represents the same set
*)

let set_union a b =
  List.append a b;;

(*
set_intersection: returns a list that represents the set created by the intersection of sets a and b
approach: we can use List.filter to filter out all elements from list a that do not exist in list b
*)
let set_intersection a b =
  List.filter (fun t -> List.exists (fun f -> f = t) b) a;;

(*
set_diff: return the list representing the set a-b
approach: use filter again, but this time filter out all the elements from list a that are found in list b
*)
let set_diff a b =
  List.filter (fun t -> List.exists (fun f -> f = t) b = false) a;;

(*
computed_fixed_point: computes the fixed point of a function using the given equality predicate and starting value
approach: we just need to recursively check if there is a fixed point by comparing (f x) and x each time. once we find a match, that is the fixed point
*)
let rec computed_fixed_point eq f x = 
  if eq (f x) x then x
  else computed_fixed_point eq f (f x);;


type ('nonterminal, 'terminal) symbol =
  | N of 'nonterminal
  | T of 'terminal;;


(*
filter_reachable : filter from g all unreachable rules
g - pair, where first element is symbol (N or T, value of symbol) and second element is list of rules
*)

let getDirectRules start rulesList =
  List.filter (fun cond -> (fst cond = start)) rulesList;; 

let rec get_symbol_values inputList =
  if inputList = [] then []
  else 
  match List.hd inputList with 
    | N nonterminal -> set_union [nonterminal] (get_symbol_values (List.tl inputList))
    | _ -> failwith "Error: tried to get symbol value for terminal symbol\n";;

let rec reachable_rhs rules output = 
  match rules with
  | [] -> output
  | hd::tl -> let reachable = List.filter (fun x -> match x with 
    | N nonterminal -> true
    | _ -> false) (snd hd) in
      reachable_rhs tl (set_union output reachable);;

let getDirectlyReachable symbol rulesList =
  let directRules = getDirectRules symbol rulesList in
  let rhs = reachable_rhs directRules [] in
  let symbolVals = get_symbol_values rhs in 
  List.cons symbol symbolVals;;

let rec findAllReachable input rulesList output = 
  match input with
  | [] -> output
  | hd::tl -> let directlyReachable = getDirectlyReachable hd rulesList in
      findAllReachable tl rulesList (set_union output directlyReachable);; 

let rec get_reachable_symbols sym rulesList = 
  computed_fixed_point equal_sets (fun s -> (findAllReachable s rulesList [])) sym;;

let filter_unreachables_out reachables rules =
  List.filter (fun cond -> let lhs = (fst cond) in
  List.mem lhs reachables) rules;;

let filter_reachable g = 
  let symbol = fst g in
  let rules = snd g in
  let reachable_symbols = get_reachable_symbols [symbol] rules in
  let filteredOutUnreachables = filter_unreachables_out reachable_symbols rules in
  (symbol, filteredOutUnreachables);;

