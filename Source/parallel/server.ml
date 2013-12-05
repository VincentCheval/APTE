module DistribData = Distrib.Distrib(Data);;

let x = Term.term_of_variable (Term.fresh_variable_from_id Term.Free "x")
and y = Term.term_of_variable (Term.fresh_variable_from_id Term.Free "y")
and z = Term.term_of_variable (Term.fresh_variable_from_id Term.Free "z")
and w = Term.term_of_variable (Term.fresh_variable_from_id Term.Free "w") in

let a = Term.term_of_name (Term.fresh_name_from_id Term.Public "a")
and b = Term.term_of_name (Term.fresh_name_from_id Term.Public "b")
and c = Term.term_of_name (Term.fresh_name_from_id Term.Public "c")
and d = Term.term_of_name (Term.fresh_name_from_id Term.Public "d")
and e = Term.term_of_name (Term.fresh_name_from_id Term.Public "e") in


DistribData.compute_job [x;y;z]
  [
    1, [(x,a); (x,b)];
    2, [(x,z); (x,b)];
    3, [(Term.apply_function Term.senc [x;a]), (Term.apply_function Term.senc [b;y])];
    4, [(Term.apply_function Term.senc [x;a]), (Term.apply_function Term.aenc [b;y])];
    5, [(a,a)];
    6, [(a,b)]
  ]
