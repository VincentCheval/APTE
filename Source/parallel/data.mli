
type shareddata = Term.term list
  
type job = int * (Term.term * Term.term) list
  
type result = bool * int * Term.substitution option
  
val initialise : shareddata -> unit
  
val evaluation : job -> result
  
val digest : result -> job list ref -> unit



