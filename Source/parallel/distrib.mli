(** This library allow to easily distribute a calculus *)

(** This is the module type for a task that need to be computed *)
module type TASK =
sig 
  type shareddata
    (** [shareddata] is a type for data needed by all the computation*)
  type job 
    (** This is the type for one job *)
  type result
    (** This is the type for the result of one job computation*)
  val initialise : shareddata -> unit
  
  val evaluation : job -> result
    (** evaluation function wich will be run on several processus*)
  val digest : result -> job list ref -> unit
    (** function to add the result of one job to the other result*)
end
  

(** This functor build a module to distribute the computation based on 
one task*)
module Distrib : functor (Task : TASK) ->
sig
  val calcfunc : unit -> unit
    (** This function launch a server that wait for data and jobs and
    return the result. This function never return*)

  val compute_job : Task.shareddata -> Task.job list -> unit
    (** [compute_job shared job] launch several processus wich run
	[calcfunc] and send them the shared data and distribute the job
	when the computation is finish all the server are closed*)

end
