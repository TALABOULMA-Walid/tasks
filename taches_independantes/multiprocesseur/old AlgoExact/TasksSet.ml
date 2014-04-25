value searchTask tasksSet i =
 let  j= ref 0 in
 while (j<= tasksSet.listTasks.length){
  if ((List.nth tasksSet.listTasks j).id=i)
  return List.nth tasksSet.listTasks j;
   i:=!i+1;
}