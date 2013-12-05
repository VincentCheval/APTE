(*let nproc = 20;;

let proctab = [| 
  "./comptrans.native" ;
  "./comptrans.native";
  "./comptrans.native";
  "./comptrans.native";
  "ssh blade09 Documents/licsextension/implementation/comptrans.native";
  "ssh blade09 Documents/licsextension/implementation/comptrans.native";
  "ssh blade09 Documents/licsextension/implementation/comptrans.native";
  "ssh blade09 Documents/licsextension/implementation/comptrans.native";
  "ssh blade10 Documents/licsextension/implementation/comptrans.native";
  "ssh blade10 Documents/licsextension/implementation/comptrans.native";
  "ssh blade10 Documents/licsextension/implementation/comptrans.native";
  "ssh blade10 Documents/licsextension/implementation/comptrans.native";
  "ssh blade11 Documents/licsextension/implementation/comptrans.native";
  "ssh blade11 Documents/licsextension/implementation/comptrans.native";
  "ssh blade11 Documents/licsextension/implementation/comptrans.native";
  "ssh blade11 Documents/licsextension/implementation/comptrans.native";
  "ssh blade12 Documents/licsextension/implementation/comptrans.native";
  "ssh blade12 Documents/licsextension/implementation/comptrans.native";
  "ssh blade12 Documents/licsextension/implementation/comptrans.native";
  "ssh blade12 Documents/licsextension/implementation/comptrans.native"|];;
*)
let nproc = 4;;
let proctab = [| "./worker" ; "./worker"; "./worker"; "./worker"|];;
  

module type TASK =
  sig
    type shareddata
    type job
    type result
    val initialise : shareddata -> unit
    val evaluation : job -> result
    val digest : result -> job list ref -> unit
  end;;


module Distrib = functor (Task:TASK) ->
  struct
    
    let calcfunc () =

      let shared = ((input_value stdin):Task.shareddata) in
      Task.initialise shared;
      
      try 
        while true do
          let job = ((input_value stdin):Task.job) in 
	  let re = Task.evaluation job in
	  output_value stdout re;
	  flush stdout;
        done
      with
        | End_of_file -> ()
	| x -> raise x

    let compute_job shared jl = 
      Unix.chdir (String.sub Sys.executable_name 0 
		    ((String.length Sys.executable_name) -
		       (String.length "worker")));
	
      let jlr = ref jl in
      let proc = 
        Array.to_list (
          Array.init nproc (fun i ->
            let (inc,outc) = Unix.open_process (proctab.(i)^" -transient") in
		  
            if !jlr <> []
            then 
              begin
                output_value outc shared;
		output_value outc (List.hd !jlr);
		flush outc;
		jlr := List.tl !jlr;
              end;
            
            (inc,outc)
          )
        )
      in
	
      let proc2 = List.map (fun (x,y) -> Unix.descr_of_in_channel x,y) proc in
      
      let lproc = ref (List.map fst proc2) in
	
      while !lproc <> [] do
        let (linc,_,_) = Unix.select !lproc [] [] (-1.) in
	   
	List.iter (fun inch -> 
	  let inch2 = Unix.in_channel_of_descr inch in
	  let re = input_value inch2 in
	  Task.digest re jlr;
		    
	  if !jlr = []
	  then 
	    lproc := List.filter (fun x -> x <> inch) !lproc
	  else 
	    begin
	      let outchan = List.assoc inch proc2 in
	      output_value outchan (List.hd !jlr);
	      flush outchan;
	      jlr := List.tl !jlr
	    end
	) linc
      done;
	
      List.iter (fun x -> ignore (Unix.close_process x)) proc

  end;;

