(*type shareddata = unit

type job = int * (Term.term * Term.term) list

type result = int * Term.substitution option

let initialise () = ()

let evaluation (n,l_term) =
  try 
    n, Some(Term.unify l_term)
  with
    Term.Not_unifiable -> n, None
    
let rec display_subst = function
  | [] -> "}"
  | [x,t] -> Printf.sprintf "%s -> %s}" (Term.display_term x) (Term.display_term t)
  | (x,t)::q -> 
      Printf.sprintf "%s -> %s, %s" (Term.display_term x) (Term.display_term t) (display_subst q)
    
let digest (n,result) job_r = match result with
  | None -> Printf.printf "Job %d : Not Unifiable\n" n
  | Some(subst) -> 
      Printf.printf "Job %d : Unifiable with the following substitution %s\n" n (display_subst (Term.equations_of_substitution subst))
      
    *)  
    
      
      

type shareddata = Term.term list

type job = int * (Term.term * Term.term) list

type result = bool * int * Term.substitution option

let test = ref ([]:shareddata)

let initialise l = test := l

let evaluation (n,l_term) =
  let r = 
    List.exists (fun (t1,t2) ->
      List.exists (fun t -> Term.is_equal_term t1 t || Term.is_equal_term t2 t) !test
    ) l_term
  in
  
  let t = try 
    r, n, Some(Term.unify l_term)
  with
    Term.Not_unifiable -> r, n, None
  in
  
  while true do
  try 
    ignore(Term.unify l_term)
  with
    Term.Not_unifiable -> ()
  done;
  t
    
let rec display_subst = function
  | [] -> "}"
  | [x,t] -> Printf.sprintf "%s -> %s}" (Term.display_term x) (Term.display_term t)
  | (x,t)::q -> 
      Printf.sprintf "%s -> %s, %s" (Term.display_term x) (Term.display_term t) (display_subst q)
    
let digest (r, n,result) job_r = 
  (*if r
  then Printf.printf "Job %d : There exists equality" n
  else Printf.printf "Job %d : There is no equality" n;*)
   
  match result with
  | None -> Printf.printf "Job %d : Not Unifiable\n" n
  | Some(subst) -> 
      job_r := (n,(Term.equations_of_substitution subst))::!job_r
      (*Printf.printf "Job %d : Unifiable with the following substitution %s\n" n (display_subst (Term.equations_of_substitution subst))*)

