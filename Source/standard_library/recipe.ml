(***************************
***         Recipe       ***
****************************)

type link = 
  | NoLink
  | RLink of recipe
  | CLink of context 
  | VLink of variable

and variable = 
  {
    id : string;
    number : int;
    support : int;
    mutable link : link;
    free : bool
  }
  
(* An axiom is defined by its support. Its id will always be "ax". *)
and axiom = int

and recipe = 
  | Var of variable
  | Axiom of axiom
  | Func of Term.symbol * recipe list
  
and path = (Term.symbol list) * axiom
  
and context = 
  | CVar of variable
  | CPath of path
  | CFunc of Term.symbol * context list
  
  
(******* General functions on list ********)  
  
let rec is_equal_list f l1 l2 = match l1,l2 with 
  | [],[] -> true
  | _,[] | [],_ -> false
  | t1::q1,t2::q2 when f t1 t2 -> is_equal_list f q1 q2
  | _,_ -> false
  
let rec order_list order_f l1 l2 = match l1,l2 with 
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | t1::q1, t2::q2 -> let ord = order_f t1 t2 in
      if ord = 0
      then order_list order_f q1 q2
      else ord    
          
let rec insert_in_sorted_list order_f elt = function
  | [] -> [elt]
  | t::q -> 
      let ord = order_f elt t in
      if ord = 0 || ord = -1
      then elt::t::q
      else t::(insert_in_sorted_list order_f elt q)
      
(*let rec insert_in_sorted_list_no_dupplicate order_f elt = function
  | [] -> [elt]
  | t::q -> 
      let ord = order_f elt t in
      if ord = 0
      then t::q 
      else if ord = -1
      then elt::t::q
      else t::(insert_in_sorted_list_no_dupplicate order_f elt q)*)
            

let rec search_and_remove f_pred = function  
  | [] -> raise Not_found
  | t::q when f_pred t -> (t,q)
  | t::q -> let (t',l) = search_and_remove f_pred q in
      (t',t::l)
      
(******** Fresh function ********)

let accumulator_variable = ref 0

let fresh_variable_from_id id support = 
  let var = 
    { 
      id = id;
      number = !accumulator_variable;
      support = support;
      link = NoLink;
      free = false
    }
  in
  accumulator_variable := !accumulator_variable + 1;
  var
  
let fresh_free_variable_from_id id support = 
  let var = 
    { 
      id = id;
      number = !accumulator_variable;
      support = support;
      link = NoLink;
      free = true
    }
  in
  accumulator_variable := !accumulator_variable + 1;
  var

let fresh_free_variable support = fresh_free_variable_from_id "X" support  
  
let fresh_variable support = fresh_variable_from_id "X" support

let axiom support = support

let rec fresh_variable_list arity support = match arity with
  | 0 -> []
  | ar -> (fresh_variable support)::(fresh_variable_list (ar-1) support)
  
let rec fresh_free_variable_list arity support = match arity with
  | 0 -> []
  | ar -> (fresh_free_variable support)::(fresh_free_variable_list (ar-1) support)
  
let rec fresh_variable_list2 arity support = match arity with
  | 0 -> []
  | ar -> (Var(fresh_variable support))::(fresh_variable_list2 (ar-1) support)
  
let order_variable v1 v2 = match v1.number with
  | v when v = v2.number -> 0
  | v when v < v2.number -> -1
  | _ -> 1  

(******** Generation of recipe ********)

let recipe_of_variable var = Var(var)

let recipe_of_axiom axiom = Axiom(axiom)

let axiom_of_recipe = function
  | Axiom i -> i
  | _ -> Debug.internal_error "[recipe.ml >> axiom_of_recipe] An axiom was expected"

let variable_of_recipe = function
  | Var v -> v
  | _ -> Debug.internal_error "[recipe.ml >> variable_of_recipe] A variable was expected"

let apply_function symbol list_sons = 
  (***[BEGIN DEBUG]***)
  Debug.low_debugging (fun () ->
    if (List.length list_sons) <> Term.get_arity symbol
    then Debug.internal_error (Printf.sprintf "[recipe.ml >> apply_function] The function %s has arity %d but is given %d recipe" (Term.display_symbol_without_arity symbol) (Term.get_arity symbol) (List.length list_sons))
  );
  (***[END DEBUG]***)

  Func(symbol,list_sons)  
  
(******** Access functions *********)  

let top = function
  | Func(f,_) -> f
  | _ -> Debug.internal_error "[recipe.ml >> top] The recipe should not be a name nor a variable"

let get_support v = v.support
    
(******** Test functions *********)

let rec occurs var = function
  | Var(v) when v == var -> true
  | Var{link = RLink t;_} -> occurs var t
  | Func(_,args) -> List.exists (occurs var) args
  | _ -> false
  
let is_equal_variable v1 v2 = v1 == v2  

let is_equal_axiom ax1 ax2 = ax1 = ax2  
  
let rec is_equal_recipe r1 r2 = match r1,r2 with
  | Var(v1),Var(v2) when v1 == v2 -> true
  | Axiom(n1),Axiom(n2) when n1 = n2 -> true
  | Func(f1,args1), Func(f2,args2) when Term.is_equal_symbol f1 f2 -> List.for_all2 is_equal_recipe args1 args2
  | _,_ -> false

let is_free_variable var = var.free

let is_free_variable2 = function
  | Var(v) -> v.free
  | _ -> false
  
let is_variable = function
  | Var(_) -> true
  | _ -> false
  
let is_axiom = function
  | Axiom(_) -> true
  | _ -> false
  
let is_function = function
  | Func(_,_) -> true
  | _ -> false

(******* Iterators ********)

let iter_args f_apply = function
  | Func(_,args) -> List.iter f_apply args
  | _ -> Debug.internal_error "[recipe.ml >> iter_args] The recipe should be an axiom nor a variable"
  
let map_args f_apply = function
  | Func(_,args) -> List.map f_apply args
  | _ -> Debug.internal_error "[recipe.ml >> map_args] The recipe should not be an axiom nor a variable"
  
(******* Substitution ********)

type substitution = (variable * recipe) list

let is_identity subst = subst = []

let create_substitution var recipe = [var,recipe]

let create_substitution2 var recipe = match var with
  | Var(v) -> [v,recipe]
  | _ -> Debug.internal_error "[recipe.ml >> create_substitution2] The recipe must be a variable"

let rec apply_substitution_on_recipe recipe = match recipe with
  | Func(f,args) -> Func(f, List.map apply_substitution_on_recipe args)
  | Var(v) -> 
      begin match v.link with
        | NoLink -> recipe
        | RLink r' -> r'
        | _ -> Debug.internal_error "[recipe.ml >> apply_substitution_on_recipe] Unexpected link"
      end
  | _ -> recipe
  
let apply_substitution subst elt f_iter_elt =
  (* Link the variables of the substitution *)
  List.iter (fun (v,t) -> v.link <- (RLink t)) subst;
  
  (* Apply the substitution on the element *)
  let new_elt = f_iter_elt elt apply_substitution_on_recipe in
  
  (* Unlink the variables of the substitution *)
  List.iter (fun (v,_) -> v.link <- NoLink) subst;
  
  new_elt
  
let equations_from_substitution = List.map (fun (v,r) -> Var(v),r)  

let filter_domain f_test subst = List.filter (fun (v,_) -> f_test v) subst

(****** Variable manipulation *******)

let linked_variables = ref []

let link var term = 
  var.link <- (RLink term);
  linked_variables := var::(!linked_variables)
  
let rec follow_link = function
  | Func(f,args) -> Func(f,List.map follow_link args)
  | Var({link = RLink t;_}) -> follow_link t
  | term -> term
  
let cleanup () =
  List.iter (fun var -> var.link <- NoLink) !linked_variables;
  linked_variables := []
  
(******* Syntactic unification *******)

exception Not_unifiable
  
let rec unify_term t1 t2 = match t1,t2 with
  | Var(v1), Var(v2) when v1 == v2 -> ()
  | Var({link = RLink t ; _}), _ -> unify_term t t2
  | _, Var({link = RLink t; _}) -> unify_term t1 t
  | Var(v1),Var(v2) ->
      if not v1.free
      then link v1 t2
      else
        if v2.free && order_variable v1 v2 = 1
        then link v1 t2
        else link v2 t1
  | Var(v1), _ -> if occurs v1 t2 then raise Not_unifiable else link v1 t2
  | _, Var(v2) -> if occurs v2 t1 then raise Not_unifiable else link v2 t1
  | Axiom(n1), Axiom(n2) when n1 == n2 -> ()
  | Func(f1,args1), Func(f2,args2) ->  
      if f1 == f2 then List.iter2 unify_term args1 args2 else raise Not_unifiable
  | _,_ -> raise Not_unifiable
  
let unify eq_list = 
  (***[BEGIN DEBUG]***)
  Debug.low_debugging (fun () ->
    if !linked_variables <> []
    then Debug.internal_error "[recipe.ml >> unify] The list of linked variables should be empty"
  );
  (***[END DEBUG]***)

  try
    List.iter (fun (t1,t2) -> unify_term t1 t2) eq_list;
    let subst = List.map (fun var -> (var,follow_link (Var var))) !linked_variables in
    cleanup ();
    subst
  with
    | exc -> 
      cleanup ();
      raise exc


(***************************
***          Path        ***
****************************)

let rec path_of_recipe recipe = match recipe with
  | Axiom(i) -> ([],i)
  | Var(_) -> Debug.internal_error "[recipe.ml >> path_of_recipe] A path of the recipe should be closed"
  | Func(f,args) when Term.is_destructor f -> 
      let (l,r) = path_of_recipe (List.hd args) in
      (f::l,r)
  | Func(_,_) -> Debug.internal_error "[recipe.ml >> path_of_recipe] A path of a recipe should only contain destructor symbols and axiom" 
  
let apply_function_to_path symb (l_symb,ax) = (symb::l_symb,ax)

let axiom_path supp = ([],supp)
  
let is_equal_path (p1,ax1) (p2,ax2) = 
  if ax1 = ax2
  then
    let rec check_symbol l1 l2 = match l1,l2 with
      | [],[] -> true
      | [],_ | _,[] -> false
      | f1::q1,f2::q2 when Term.is_equal_symbol f1 f2 -> check_symbol q1 q2
      | _,_ -> false
    in
    
    check_symbol p1 p2
  else false
  
let rec is_recipe_same_path r1 r2 = match r1,r2 with
  | Axiom(i1), Axiom(i2) when i1 = i2 -> true
  | Func(f1,args1), Func(f2,args2) when (Term.is_equal_symbol f1 f2) && (Term.is_destructor f1) ->
      is_recipe_same_path (List.hd args1) (List.hd args2)
  | _,_ -> false
  
let rec is_path_of_recipe recipe (l,ax) = match l,recipe with
  | [],Axiom(i) when i = ax -> true
  | [],_ -> false
  | f1::q,Func(f2,args) when Term.is_equal_symbol f1 f2 ->
      is_path_of_recipe (List.hd args) (q,ax)
  | _,_ -> false
  
let order_path path1 path2 = match path1,path2 with
  | (f_list1,ax1),(f_list2,ax2) when ax1 = ax2 -> order_list Term.order_symbol f_list1 f_list2
  | (_,ax1),(_,ax2) -> compare ax1 ax2  
    
(*******************************
***          Context         ***
********************************)

let top_context = function
  | CFunc(f,_) -> f
  | _ -> Debug.internal_error "[recipe.ml >> top_context] The context should not be a path nor a variable"
  
let path_of_context = function
  | CPath p -> p
  | _ -> Debug.internal_error "[recipe.ml >> path_of_context] The context should be a path"

let rec context_of_recipe = function
  | Var(v) -> CVar(v)
  | Func(f,args) when Term.is_constructor f -> CFunc(f,List.map context_of_recipe args)
  | r -> CPath(path_of_recipe r) 
  
let rec recipe_of_context = function
  | CVar(v) -> Var(v)
  | CFunc(f,args) -> Func(f,List.map recipe_of_context args)
  | CPath _ -> Debug.internal_error "[recipe.ml >> recipe_of_context] The context should not contain any path"

(* Access *)

let rec get_max_param_context = function
  | CVar(v) -> v.support
  | CFunc(_,args) -> List.fold_left (fun acc pr -> max acc (get_max_param_context pr)) 0 args
  | CPath (_,i) -> i 
  
(* Testing *)

let rec is_closed_context = function
  | CVar(_) -> false
  | CPath(_) -> true
  | CFunc(_,args) -> List.for_all is_closed_context args  
  
let is_variable_context = function
  | CVar _ -> true
  | _ -> false
  
let is_path_context = function
  | CPath(_) -> true
  | _ -> false
  
let rec exists_path_in_context = function
  | CVar _ -> false
  | CPath _ -> true
  | CFunc(_,args) -> List.exists exists_path_in_context args

(** Substitution *)
  
let rec apply_substitution_on_pr = function
  | CFunc(f,args) -> CFunc(f, List.map apply_substitution_on_pr args)
  | CVar(v) -> 
      begin match v.link with
        | NoLink -> CVar(v)
        | CLink r' -> r'
        | _ -> Debug.internal_error "[recipe.ml >> apply_substitution_on_pr] Unexpected link"
      end
  | pr -> pr
  
let apply_substitution_on_context subst elt f_iter_elt =
  (* Link the variables of the substitution *)
  List.iter (fun (v,t) -> v.link <- (CLink (context_of_recipe t))) subst;
  
  (* Apply the substitution on the element *)
  let new_elt = f_iter_elt elt apply_substitution_on_pr in
  
  (* Unlink the variables of the substitution *)
  List.iter (fun (v,_) -> v.link <- NoLink) subst;
  
  new_elt
  
(*******************************
***         Formulas         ***
********************************)

exception Removal_transformation

type formula = (context * context) list

let create_formula var recipe = [CVar(var),context_of_recipe recipe]

let for_all_formula = List.for_all 

let exists_formula = List.exists  

let rec find_and_apply_formula f_test f_apply f_no_result = function
  | [] -> f_no_result ()
  | (t1,t2)::q -> 
      let r_test = f_test t1 t2 in
      if r_test
      then f_apply t1 t2
      else find_and_apply_formula f_test f_apply f_no_result q

(****** Simplification *******)      
      
let rec semi_unify all_path ref_list pr1 pr2 = match pr1,pr2 with
  | CVar(v1),CVar(v2) when v1 == v2 -> ()
  | CVar(_),CVar(_) | CVar(_), CFunc(_) -> 
      all_path := false;
      ref_list := (pr1,pr2)::!ref_list
  | CFunc(_),CVar(_) -> 
      all_path := false;
      ref_list := (pr2,pr1)::!ref_list
  | CVar(_),CPath(_) -> ref_list := (pr1,pr2)::!ref_list
  | CPath(_),CVar(_) -> ref_list := (pr2,pr1)::!ref_list
  | CPath(p1),CPath(p2) when is_equal_path p1 p2 -> ()
  | CFunc(f1,args1),CFunc(f2,args2) -> 
      if not (Term.is_equal_symbol f1 f2)
      then  Debug.internal_error "[recipe.ml >> semi_unify] The inequation disjunction should never be true";
      
      List.iter2 (semi_unify all_path ref_list) args1 args2
  | _,_ -> ref_list := (pr1,pr2)::!ref_list
  
let simplify_formula list_neq = 
  let ref_list = ref [] in
  let all_path = ref true in
  List.iter (fun (pr1,pr2) -> semi_unify all_path ref_list pr1 pr2) list_neq;
  if !all_path
  then raise Removal_transformation
  else !ref_list
  
(******* Substitution *******)  
  
let rec apply_substitution_on_context2 (v,pt) = function
  | CVar(v') when v == v' -> pt
  | CFunc(f,args) -> CFunc(f,List.map (apply_substitution_on_context2 (v,pt)) args)
  | pr -> pr
  
let rec apply_substitution_on_context_change_detected ref_change (v,pt) = function
  | CVar(v') when v == v' -> ref_change := true; pt
  | CFunc(f,args) -> CFunc(f,List.map (apply_substitution_on_context_change_detected ref_change (v,pt)) args)
  | pr -> pr
  
let apply_substitution_on_formulas subst elt f_iter_elt = match subst with
  | [v,recipe] -> let pt = context_of_recipe recipe in
      f_iter_elt elt (fun list_neq -> 
        List.map (fun (pt1,pt2) -> 
          apply_substitution_on_context2 (v,pt) pt1,
          apply_substitution_on_context2 (v,pt) pt2
        ) list_neq
      )
  | _ -> Debug.internal_error "[recipe.ml >> apply_substitution_on_formulas] The domain of the subtitution should contain only one variable"

let apply_simplify_substitution_on_formulas subst elt f_iter_elt = match subst with
  | [v,recipe] -> let pt = context_of_recipe recipe in
      f_iter_elt elt (fun list_neq -> 
        let was_modified = ref false in
        
        let formula' = 
          List.map (fun (pt1,pt2) -> 
            apply_substitution_on_context_change_detected was_modified (v,pt) pt1,
            apply_substitution_on_context_change_detected was_modified (v,pt) pt2
          ) list_neq
        in
          
        if !was_modified
        then simplify_formula formula'
        else list_neq
      )
  | _ -> Debug.internal_error "[recipe.ml >> apply_substitution_on_formulas] The domain of the subtitution should contain only one variable"
  
  
(***************************************
***         General Formulas         ***
****************************************)  

(* The term symbol list and path symbol list should be always ordered *)
type atomic_formula = 
  | Neq of variable * Term.symbol list * path list
  | Eq of variable * context

(** The first list corresponds to the existential variables.
    The second element is disjunction of conjunction of atomic formulas.*)
type 'a general_formula =
  {
    elt: 'a;
    neg_to_remove : variable list;
    formula : atomic_formula list
  }

type 'a partition_elt =
  | PartVar of variable * 'a general_formula list
  | PartPath of path * 'a general_formula list
  | PartSymb of Term.symbol * variable list * 'a general_formula list
  | PartNeq of Term.symbol list * path list * 'a general_formula list
  | PartEmpty of 'a general_formula list

(******* Order functions *********)

let order_atomic atm1 atm2 = match atm1,atm2 with
  | Eq(v1,_),Neq(v2,_,_) -> 
      let ord = order_variable v1 v2 in
      if ord = 0
      then 1
      else ord
  | Neq(v1,_,_),Eq(v2,_) -> 
      let ord = order_variable v1 v2 in
      if ord = 0
      then -1
      else ord
  | Neq(v1,f_list1,p_list1),Neq(v2,f_list2,p_list2) -> 
      let ord1 = order_variable v1 v2 in
      if ord1 = 0 
      then 
        let ord2 = order_list Term.order_symbol f_list1 f_list2 in
        if ord2 = 0
        then order_list order_path p_list1 p_list2
        else ord2
      else ord1
  | Eq(v1,_),Eq(v2,_) -> order_variable v1 v2
  
(******* Manipulation of variables *********)
  
let linked_variables_var = ref []

let link_var var1 var2 = 
  var1.link <- (VLink var2);
  linked_variables_var := var1::(!linked_variables_var)
  
let rec follow_link_var = function
  | CFunc(f,args) -> CFunc(f,List.map follow_link_var args)
  | CVar({link = VLink v;_}) -> CVar(v)
  | context -> context
  
let cleanup_var () =
  List.iter (fun var -> var.link <- NoLink) !linked_variables_var;
  linked_variables_var := []  
    
(******* Partition functions *********)
  
let rec add_formula_in_partition_from_eq elt neg_to_remove target_var context atm_list partition = match partition,context with
  | [], CVar(var) ->
      if var.free
      then [PartVar (var,[{ elt = elt; neg_to_remove = neg_to_remove; formula = atm_list}])]
      else 
        begin
          var.link <- VLink target_var;
          let general_formula = 
            { 
              elt = elt;
              neg_to_remove = neg_to_remove;
              formula = List.map (function 
                | Neq({link = VLink v;_},f_list,p_list) -> Neq(v,f_list,p_list)
                | Neq(v,f_list,p_list) -> Neq(v,f_list,p_list)
                | Eq(v,context) -> Eq(v,follow_link_var context)
              ) atm_list
            }
          in
          var.link <- NoLink;
          [PartEmpty [general_formula]] 
        end
        
  | [],CPath(path) -> [PartPath (path, [{ elt = elt; neg_to_remove = neg_to_remove; formula = atm_list}])]
  
  | [],CFunc(symb,c_list) -> 
      let support = get_support target_var in
      let arity = Term.get_arity symb in
      let list_var = fresh_free_variable_list arity support in
            
      let new_atm_list = List.fold_right2 (fun v c at_l -> (Eq (v,c))::at_l) list_var c_list atm_list in
      let general_formula = { elt = elt; neg_to_remove = neg_to_remove; formula = new_atm_list} in
      
      [PartSymb (symb,list_var,[general_formula])]
      
  | PartVar(var,l)::q,CVar(var') when is_equal_variable var var' -> 
      let general_formula = { elt = elt; neg_to_remove = neg_to_remove; formula = atm_list} in
      (PartVar (var,general_formula::l))::q
      
  | PartEmpty(l)::q,CVar(var) when not var.free -> 
      var.link <- VLink target_var;
      let general_formula = 
        { 
          elt = elt;
          neg_to_remove = neg_to_remove;
          formula = List.map (function 
            | Neq({link = VLink v;_},f_list,p_list) -> Neq(v,f_list,p_list)
            | Neq(v,f_list,p_list) -> Neq(v,f_list,p_list)
            | Eq(v,context) -> Eq(v,follow_link_var context)
          ) atm_list
        }
      in
      var.link <- NoLink;
      (PartEmpty (general_formula::l))::q
      
  | PartPath(path,l)::q, CPath(path') when is_equal_path path path' -> 
      let general_formula = { elt = elt; neg_to_remove = neg_to_remove; formula = atm_list} in
      (PartPath(path,general_formula::l))::q
      
  | PartSymb(symb,v_list,l)::q, CFunc(symb',c_list) when Term.is_equal_symbol symb symb' ->
      let new_atm_list = List.fold_right2 (fun v c at_l -> (Eq (v,c))::at_l) v_list c_list atm_list in
      let general_formula = { elt = elt; neg_to_remove = neg_to_remove; formula = new_atm_list} in
      (PartSymb (symb,v_list,general_formula::l))::q
      
  | t::q, _ -> t::(add_formula_in_partition_from_eq elt neg_to_remove target_var context atm_list q)
  
  
let rec add_formula_in_partition_from_neq elt neg_to_remove atm_list (symb_l,path_l) = function
  | [] -> 
      let general_formula = { elt = elt; neg_to_remove = neg_to_remove; formula = atm_list} in
      [PartNeq (symb_l,path_l, [general_formula])]
      
  | PartNeq (symb_l',path_l',form_l)::q when 
    is_equal_list Term.is_equal_symbol symb_l symb_l' && 
    is_equal_list is_equal_path path_l path_l' -> 
      let general_formula = { elt = elt; neg_to_remove = neg_to_remove; formula = atm_list} in
      (PartNeq (symb_l,path_l, general_formula::form_l))::q
      
  | t::q -> t::(add_formula_in_partition_from_neq elt neg_to_remove atm_list (symb_l,path_l) q)
  
let rec add_formula_in_partition_from_empty general_formula = function 
  | [] -> [PartEmpty [general_formula]]
  | PartEmpty(l)::q -> (PartEmpty (general_formula::l))::q
  | t::q -> t::(add_formula_in_partition_from_empty general_formula q)

let rec partitionate target_var = function
  | [] -> []
  | general_formula::q ->
      let current_partition = partitionate target_var q in
      
      let rec generate_new_partition atm_list = function
        | [] -> add_formula_in_partition_from_empty general_formula current_partition
        | Neq(var,symb_l,path_l)::q' when is_equal_variable var target_var -> 
            add_formula_in_partition_from_neq 
              general_formula.elt 
              general_formula.neg_to_remove 
              (atm_list@q')
              (symb_l,path_l) 
              current_partition
        | Eq(var,context)::q' when is_equal_variable var target_var -> 
            add_formula_in_partition_from_eq 
              general_formula.elt 
              general_formula.neg_to_remove target_var 
              context 
              (atm_list@q')
              current_partition
        | t::q' -> generate_new_partition (t::atm_list) q'
      in
      
      (generate_new_partition [] general_formula.formula)  

      
      

  
  
(* The not free variables should be disjoint in c1 and c2. *)
let rec is_equal_context c1 c2 = match c1,c2 with
  | CVar(v1),CVar(v2) when v1 == v2 && v1.free-> true
  | CVar(v1),CVar(v2) when v1 == v2 && v1.free = false -> Debug.internal_error "[recipe.ml >> is_equal_context] Existential variables not distinct"
  | CVar(v1),CVar(v2) when v1.free = false && v2.free = false ->
      begin match v1.link with
        | VLink(v3) when v2 == v3 -> true
        | VLink(_) -> false
        | NoLink -> link_var v1 v2; true
        | _ -> Debug.internal_error "[recipe.ml >> is_equal_context] Wrong type of link"
      end
  | CPath(p1),CPath(p2) when is_equal_path p1 p2 -> true
  | CFunc(f1,c_list1), CFunc(f2,c_list2) when Term.is_equal_symbol f1 f2 -> List.for_all2 is_equal_context c_list1 c_list2
  | _,_ -> false
       
(* The formula should be ordered *)
let rec is_equal_formula formula1 formula2 = match formula1, formula2 with
  | [],[] -> cleanup_var (); true
  | Eq(v1,c1)::q1, Eq(v2,c2)::q2 when is_equal_variable v1 v2 && is_equal_context c1 c2 -> is_equal_formula q1 q2
  | Neq(v1,f_list1,p_list1)::q1,Neq(v2,f_list2,p_list2)::q2 when 
    is_equal_variable v1 v2 && 
    is_equal_list Term.is_equal_symbol f_list1 f_list2 &&
    is_equal_list is_equal_path p_list1 p_list2 ->
      is_equal_formula q1 q2
  | _,_ -> false
  
let is_equal_general_formula g_formula1 g_formula2 = 
  if !linked_variables_var <> []
  then Debug.internal_error "[recipe.ml >> equal_general_formula] The linked variables list should be empty"
  else is_equal_formula g_formula1.formula g_formula2.formula
 
let search_target_var general_formula_list = 

  let result = ref None in
  
  let rec sub_search = function
    | [] -> ()
    | form::_ when List.exists (function | Eq(v,_) -> result := Some(v); true | _ -> false) form.formula -> ()
    | _::q -> sub_search q
  in
  
  sub_search general_formula_list;
  match !result with
    | None -> raise Not_found
    | Some(v) -> v

(******** Factorisation **********)

let rec factorise_general_formulas general_form_list =
  if general_form_list = []
  then []
  else
    
    try
      (* Find a target var *)
      let target_var = search_target_var general_form_list in
      
      (* Create the partition *)
      let partition  = partitionate target_var general_form_list in
      
      (* Factorise the formulas in the partition *)
      let partition_factorised = List.map (function
        | PartVar(v,g_form_l) -> PartVar(v,factorise_general_formulas g_form_l)
        | PartPath(p,g_form_l) -> PartPath(p,factorise_general_formulas g_form_l)
        | PartSymb(f,v_list,g_form_l) -> PartSymb(f,v_list,factorise_general_formulas g_form_l)
        | PartNeq(f_list,p_list,g_form_l) -> PartNeq(f_list,p_list,factorise_general_formulas g_form_l)
        | PartEmpty(g_form_l) -> PartEmpty(factorise_general_formulas g_form_l)
        ) partition in
      
      (* Generate reference for correspondance *)
      let partsymb = ref [] 
      and partempty = ref []
      and partneq = ref []
      and partpath = ref []
      and partvar = ref [] in
      
      (* Insert Partition *)
      List.iter (function
        | PartVar(v,g_form_l) -> partvar := (v,g_form_l) :: !partvar
        | PartPath(p,g_form_l) -> partpath := insert_in_sorted_list (fun (p1,_) (p2,_) -> order_path p1 p2) (p,g_form_l) !partpath
        | PartSymb(f,v_list,g_form_l) -> partsymb := insert_in_sorted_list (fun (f1,_,_) (f2,_,_) -> Term.order_symbol f1 f2) (f,v_list,g_form_l) !partsymb
        | PartNeq(f_list,p_list,g_form_l) -> partneq := (f_list,p_list,g_form_l) :: !partneq
        | PartEmpty(g_form_l) -> partempty := g_form_l
        ) partition_factorised;
        
      (* Searching the  correspondance *)
      
      (* 1 - Verify the empty *)
      
      List.iter (fun g_form_1 -> 
        partvar := List.map (fun (v,g_form_l_2) -> (v,List.filter (fun g_form_2 -> not (is_equal_general_formula g_form_1 g_form_2)) g_form_l_2)) !partvar; 
        partpath := List.map (fun (p,g_form_l_2) -> (p,List.filter (fun g_form_2 -> not (is_equal_general_formula g_form_1 g_form_2)) g_form_l_2)) !partpath; 
        partsymb := List.map (fun (f,v_list,g_form_l_2) -> (f,v_list,List.filter (fun g_form_2 -> not (is_equal_general_formula g_form_1 g_form_2)) g_form_l_2)) !partsymb; 
        partneq := List.map (fun (f_list,p_list,g_form_l_2) -> (f_list,p_list,List.filter (fun g_form_2 -> not (is_equal_general_formula g_form_1 g_form_2)) g_form_l_2)) !partneq
        ) !partempty;
        
      (* 2 - Search the neq *)
      
      let rec search_matching_symbol f_list g_form partition_symb = match f_list, partition_symb with
        | [],_ -> Some(partition_symb)
        | _,[] -> None
        | symb::q_symb, (symb',v_list,g_form_l)::q_part when Term.is_equal_symbol symb symb' ->
            let (l_equal,l_neq) = List.partition (is_equal_general_formula g_form) g_form_l in
            
            begin match l_equal with
              | [] -> None
              | [_] -> 
                  begin match search_matching_symbol q_symb g_form q_part with
                    | None -> None
                    | Some(new_partition) -> Some((symb,v_list,l_neq)::new_partition)
                  end
              | _ -> Debug.internal_error "[recipe.ml >> factorise_general_formulas] There should not be more than one element in the list (1)"
            end  
        | symb::_, (symb',v_list,g_form_l)::q_part when Term.order_symbol symb symb' = -1 -> 
            begin match search_matching_symbol f_list g_form q_part with
              | None -> None
              | Some(new_partition) -> Some((symb',v_list,List.filter (fun g_form_2 -> not (is_equal_general_formula g_form g_form_2)) g_form_l)::new_partition)
            end
        | _,_ -> None
      in
      
      let rec search_matching_path p_list g_form partition_path = match p_list, partition_path with
        | [],_ -> Some(partition_path)
        | _,[] -> None
        | path::q_path, (path',g_form_l)::q_part when is_equal_path path path' ->
            let (l_equal,l_neq) = List.partition (is_equal_general_formula g_form) g_form_l in
            
            begin match l_equal with
              | [] -> None
              | [_] -> 
                  begin match search_matching_path q_path g_form q_part with
                    | None -> None
                    | Some(new_partition) -> Some((path,l_neq)::new_partition)
                  end
              | _ -> Debug.internal_error "[recipe.ml >> factorise_general_formulas] There should not be more than one element in the list (2)"
            end  
        | path::_, (path',g_form_l)::q_part when order_path path path' = -1 -> 
            begin match search_matching_path p_list g_form q_part with
              | None -> None
              | Some(new_partition) -> Some((path',List.filter (fun g_form_2 -> not (is_equal_general_formula g_form g_form_2)) g_form_l)::new_partition)
            end
        | _,_ -> None
      in
      
      let pre_partneq = ref [] in
      
      let rec search_sub_neq f_list p_list = function
        | [] -> []
        | g_form::g_form_l -> 
            begin match search_matching_symbol f_list g_form !partsymb with
              | None -> g_form::(search_sub_neq f_list p_list g_form_l)
              | Some(new_partsymb) ->
                  begin match search_matching_path p_list g_form !partpath with
                    | None -> g_form::(search_sub_neq f_list p_list g_form_l)
                    | Some(new_partpath) ->
                        let new_g_form = 
                          {
                            elt = g_form.elt;
                            neg_to_remove = target_var::g_form.neg_to_remove;
                            formula = g_form.formula
                          } in
                        
                        partvar := List.map (fun (v,g_form_l_2) -> (v,List.filter (fun g_form_2 -> not (is_equal_general_formula new_g_form g_form_2)) g_form_l_2)) !partvar;
                        pre_partneq := List.map (fun (f_list',p_list',g_form_l_2) -> (f_list',p_list',List.filter (fun g_form_2 -> not (is_equal_general_formula g_form g_form_2)) g_form_l_2)) !pre_partneq;
                        partneq := List.map (fun (f_list',p_list',g_form_l_2) -> (f_list',p_list',List.filter (fun g_form_2 -> not (is_equal_general_formula g_form g_form_2)) g_form_l_2)) !partneq;
                        partsymb := new_partsymb;
                        partpath := new_partpath;
                        partempty := new_g_form :: !partempty;
                        
                        search_sub_neq f_list p_list g_form_l
                  end
            end
      in
      
      let rec search_neq () = match !partneq with
        | [] -> partneq := !pre_partneq;
            pre_partneq := []
        | (f_list,p_list,g_form_l)::q ->
            partneq := q;
            let new_g_form_l = search_sub_neq f_list p_list g_form_l in
            
            if new_g_form_l <> []
            then pre_partneq := (f_list,p_list,new_g_form_l) :: !pre_partneq;
            
            search_neq ()
      in
       
      search_neq ();
      
      (* 3 - Generate the new general formulas *)
      
      let list_general_formula_1 = 
        List.fold_left (fun acc (v,g_form_l) ->
          List.fold_left (fun acc' g_form -> 
            { g_form with formula = insert_in_sorted_list order_atomic (Eq (target_var,CVar v)) g_form.formula } :: acc'
          ) acc g_form_l
        ) [] !partvar
      in
      
      let list_general_formula_2 =
        List.fold_left (fun acc (path,g_form_l) ->
          List.fold_left (fun acc' g_form -> 
            { g_form with formula = insert_in_sorted_list order_atomic (Eq (target_var,CPath path)) g_form.formula } :: acc'
          ) acc g_form_l
        ) list_general_formula_1 !partpath
      in
      
      let list_general_formula_3 = List.fold_left (fun acc g_form -> g_form::acc) list_general_formula_2 !partempty in
      
      let list_general_formula_4 = 
        List.fold_left (fun acc (f_list,p_list,g_form_l) ->
          List.fold_left (fun acc' g_form -> 
            { g_form with formula = insert_in_sorted_list order_atomic (Neq (target_var,f_list,p_list)) g_form.formula } :: acc'
          ) acc g_form_l
        ) list_general_formula_3 !partneq
      in
      
      let list_general_formula_5 = 
        List.fold_left (fun acc (symb,v_list,g_form_l) ->
          List.fold_left (fun acc' g_form -> 
            let (context_args,new_formula) = List.fold_right (fun var (c_list,formula) ->
              try
                let (atm,new_formula) = search_and_remove (function 
                  | Eq (var',_) when is_equal_variable var var' -> true
                  | _ -> false
                ) formula in
                
                let context = match atm with 
                  | Eq(_,c) -> c
                  | _ -> Debug.internal_error "[recipe.ml > factorise_formula] This case should not happen"
                in
                
                (context::c_list,new_formula)
              with Not_found -> (CVar(var)::c_list,formula)
              ) v_list ([],g_form.formula)
            in
            
            let new_formula' = insert_in_sorted_list order_atomic (Eq(target_var,CFunc(symb,context_args))) new_formula in
            
            { g_form with formula = new_formula' } :: acc'
          ) acc g_form_l
        ) list_general_formula_4 !partsymb
      in
      
      list_general_formula_5
    with
      Not_found -> general_form_list
      
(********* Existentialise formula *********)

let rec existentialise_context free_vars = function
  | CVar({ link = VLink v;_}) -> CVar(v) 
  | CVar(var) when List.exists (is_equal_variable var) free_vars -> CVar(var)
  | CVar(var) -> 
      let new_var = fresh_variable (get_support var) in
      link_var var new_var;
      CVar(new_var)
  | CFunc(f,c_list) -> CFunc(f,List.map (existentialise_context free_vars) c_list)
  | c -> c
      
let existentialise_atomic_formula free_vars = function
  | Neq({link = VLink v;_},f_list,p_list) -> Neq(v,f_list,p_list)
  | Neq(var,f_list,p_list) when List.exists (is_equal_variable var) free_vars -> Neq(var,f_list,p_list)
  | Neq(var,f_list,p_list) -> 
      let new_var = fresh_variable (get_support var) in
      link_var var new_var;
      Neq(new_var,f_list,p_list)
  | Eq({link = VLink v;_},context) -> Eq(v,existentialise_context free_vars context)
  | Eq(var,context) when List.exists (is_equal_variable var) free_vars -> Eq(var,existentialise_context free_vars context)
  | Eq(var,context) ->
      let new_var = fresh_variable (get_support var) in
      link_var var new_var;
      Eq(new_var,existentialise_context free_vars context)
      
let existentialise_general_formula free_vars g_form =
  let new_formula = List.map (existentialise_atomic_formula free_vars) g_form.formula in
  cleanup_var ();
  { g_form with formula = new_formula }
  
(******* Generation of general_formula *******)  
    
let create_general_formula free_vars equation_recipe negation_list elt = 
  
  let subst = unify equation_recipe in
  let subst' = filter_domain (fun v -> List.exists (is_equal_variable v) free_vars) subst in
  
  let formula = List.map (fun (v,r) -> Eq(v,context_of_recipe r)) subst' in
  
  let formula' = List.fold_left (fun acc (x,f_list,p_list) -> Neq(x,f_list,p_list)::acc) formula negation_list in
  
  let g_form = 
    {
      elt = elt;
      neg_to_remove = [];
      formula = formula'
    } in
  
  existentialise_general_formula free_vars g_form
  
let get_variable_to_remove_from_general_formula g_form = g_form.neg_to_remove

let get_elt_from_general_formula g_form = g_form.elt
  
  
(*******************************
***         Display          ***
********************************)

let display_variable v = 
  if v.free
  then Printf.sprintf "%s^F_%d" v.id v.number
  else Printf.sprintf "%s^B_%d" v.id v.number
  
let display_axiom ax = Printf.sprintf "ax_%d" ax

let rec display_list_recipe f_apply = function
  | [] -> ""
  | [t] -> f_apply t
  | t::q -> Printf.sprintf "%s,%s" (f_apply t) (display_list_recipe f_apply q)

let rec display_recipe = function
  | Var(v) -> display_variable v
  | Axiom(ax) -> display_axiom ax
  | Func(f,args) -> 
      Printf.sprintf "%s(%s)" (Term.display_symbol_without_arity f) (display_list_recipe display_recipe args)     
      
and display_recipe2 assoc f_apply = function
  | Var(v) -> 
      begin try
        let _,t = List.find (fun (r,_) -> is_equal_recipe r (Var v)) assoc in
        f_apply t
      with
        Not_found -> display_variable v
      end
  | Axiom(ax) -> 
      begin try
        let _,t = List.find (fun (r,_) -> is_equal_recipe r (Axiom ax)) assoc in
        f_apply t
      with
        Not_found -> display_axiom ax
      end
  | Func(f,args) -> 
      Printf.sprintf "%s(%s)" (Term.display_symbol_without_arity f) (display_list_recipe (display_recipe2 assoc f_apply) args)
      
let display_path (l,ax) = 
  List.fold_right (fun f str->
    (Term.display_symbol_without_arity f)^":"^str
  ) l (display_axiom ax)
  
let rec display_context = function
  | CVar(v) -> display_variable v
  | CPath(p) -> display_path p
  | CFunc(f,args) -> Printf.sprintf "%s(%s)" (Term.display_symbol_without_arity f) (display_list_recipe display_context args) 
  
let rec display_formula = function
  | [] -> "BotF"
  | [c1,c2] -> (display_context c1)^" <> "^(display_context c2)
  | (c1,c2)::q -> (display_context c1)^" <> "^(display_context c2)^" \\/ "^(display_formula q)
  
  
let display_atomic_formula = function
  | Neq(_,[],[]) -> ""
  | Neq(var,[],p::q) -> Printf.sprintf "%s <> %s%s" (display_variable var) (display_path p) (
      List.fold_right (fun path acc -> Printf.sprintf " /\\ %s <> %s%s" (display_variable var) (display_path path) acc) q "")
  | Neq(var,f::q_f,p_list) ->
      Printf.sprintf "Root(%s) <> %s%s%s" 
        (display_variable var)
        (Term.display_symbol_without_arity f) 
        (List.fold_right (fun f' acc -> Printf.sprintf " /\\ Root(%s) <> %s%s" (display_variable var) (Term.display_symbol_without_arity f') acc) q_f "")
        (List.fold_right (fun path acc -> Printf.sprintf " /\\ %s <> %s%s" (display_variable var) (display_path path) acc) p_list "")
  | Eq(var,context) -> Printf.sprintf "%s = %s" (display_variable var) (display_context context)

let display_general_formula g_form = match g_form.formula with
  | [] -> "true"
  | t::q -> 
      Printf.sprintf "%s%s" 
        (display_atomic_formula t) 
        (List.fold_right (fun atm acc -> Printf.sprintf " /\\ %s%s" (display_atomic_formula atm) acc) q "")
      
(***********************************
***        Mapping function      ***
************************************)

module IntComp =
struct
  type t = int
  let compare = compare
end

module IntMap = Map.Make(IntComp)

module VariableMap =
struct
  type 'a map = 'a IntMap.t
  
  let empty = IntMap.empty
  
  let is_empty = IntMap.is_empty
  
  let add v = IntMap.add v.number
  
  let find v = IntMap.find v.number
  
  let mem v = IntMap.mem v.number
end
