value exactAlgorithm tasksSet processorsSet =
 let schedulable = ref true in 
(* Supposant que la liste des tâches est dans le bon ordre *)
 let t1 =(List.nth tasksSet.listTasks 0) in 
 let processor ={id=1;listTasks=[t1.id]; stask=;responseTime=t1.wcet} in
 let listSolutions =ref list (list [processor]) in 
 let stop= ref 1 in
while ((!stop)!=taskSet.listTasks.length) &( schedulable=true) do {
  let task= List.nth tasksSet stop in
  let listSol= ref  list (list []) in  
  let sched= ref false in 
  for i =0 to listSolutions.length do {
   let size= ref (List.nth listSolutions i).length in  
   if (size<processorsSet.listProcessor.length)
   {listSolutions:=listSolutions @ [{id=(size+1);listTasks=[]; stask=;responseTime=0}];
    size:=(!size)+1 ;
   } 
    let sol= (List.nth listSolutions i) in 
    for j=0 to sol.length do{
      if((testOnProcessor (List.nth sol j) task)=true){
       sched:=true ;
       let newParSolution= newParSolution sol  stop i in 
       listSol:= (!listSol) @ [newParSolution] 
      }
    } 
  }
  if(!sched=true)
    listSolutions:=listSol;
  else
    schedulable=false;
} (* Fin boucle while*)
let min = ref 
 
  