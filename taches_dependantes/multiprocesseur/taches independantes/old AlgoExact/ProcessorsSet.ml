value newPartSolution listProc idTask- idProc = (* pour creer une solution parielle en ajoutant la tâche idTask sur le processeur idProc*) 
 let listP = ref list [] in
 for i=0 to listProc.length do {
   listP:= (!listP) @ [(List.nth listProc i)] ;
   if i=idProc do {
    (List.nth listP i).listTasks-<((List.nth listP i).listTasks @[idTask]) in                 
   }  
}
return listP ;

