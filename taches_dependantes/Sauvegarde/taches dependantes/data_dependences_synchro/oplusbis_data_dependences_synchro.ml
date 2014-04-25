(* Définition des types *)
(* type task =
{istart_time :  int ;
 itrans : int;
 perm  :int;
 schedule : int array ;
 schedulable: bool;
 loadT :float;
 wrt : int
(* makespan : int;*)
}*)



type task =
{id : int ;
 mutable firstActivation :int;
 wcet : int;
 period: int;
 deadline: int;
 preemption_cost: int ;
 mutable priority : float;
 mutable ci_t: int;
 mutable di_t: int;
 mutable bi_t: int;
 mutable lpred: task list;
 mutable lsucc: task list; 
 mutable indice: int; 
 mutable priority_t : float;  
 mutable lbuffer : buffer_b list;
 mutable set_blocked_tasks : task list
(* mutable lbuffer_t : buffer_b list;*)
(*mutable ci_t: int array;
 mutable di_t: int array;*)
 (*wrtTask : int ;*)
}
and 

buffer_b=
{idBuf:int;
 priority_buf: float;
 setTasks_may_use_b : task list;
 (*setTasks_currently_used : task list;*)
}



type processeur=
{idproc : int;
 (*mutable t : task list ;*)
(*mutable schedule  : int array;*)
 mutable phi_t : int array;
 mutable schedulable : bool;
 mutable idSelectedTask_t: int;
 mutable idSelectedTask_t_1: int;
 mutable list_t : int list;
 mutable t: int;
 mutable t_1 :int;
 mutable next_t: int;
 mutable selectedTask: task
 (*mutable load: float ;*)
}

type type_metier=
{tasks_currently_used_buffers: task list;
 buffer_curently_used_t : buffer_b list;
 priority_system_t: float;
 
}

type interval=
{r_min: int ;
f_interval: int;
}

type result=
{ proc : processeur;
  ltask : task list ; 
  met : type_metier;
}

type result_parse=
{ litasks:task list;
  load:float;
}
(*
type pred_succ_t=
{ t_p:int;
  t_s:int;
}

 type resultHeuristic =
{lprocesseurs : processeur list ;
  sched : bool;
  loadTasks : float;
  setWRT : int 
}
*)

(*
let setFrtWrt t frt wrt =
{id=t.id;firstActivation=t.firstActivation;wcet=t.wcet;period=t.period;deadline=t.deadline;preemption_cost=t.preemption_cost;wrtTask=t.wrtTask};;

let compute_start_time ot t =
min ot.istart_time t.firstActivation;;
(****************************************************************************************)
let compute_trans_part ot t=
let trans= ref  t.firstActivation in 
while !trans < ot.istart_time do 
   trans:=(!trans) + t.period
  done;
(!trans);;

*)




(*********************** Priority buffer *************************)
let priority_buffer setTasks_may_use_b=
let i=ref 0 in 
let max= ref min_float in

while (!i< (List.length setTasks_may_use_b)) do 
let priority=(List.nth setTasks_may_use_b !i).priority in
if( priority>(!max)) then 
  max:= priority;
 i:=(!i)+1;
done;
!max;;

(*********************** Priority ti à t  *************************)
let rec priority_ti_t ti set_blocked_tasks=
if(set_blocked_tasks=[]) then 
 ti.priority
else
begin
 let i=ref 0 in 
 let max=ref min_float in 
 while (!i< (List.length set_blocked_tasks)) do 
 let priority=(priority_ti_t (List.nth set_blocked_tasks !i) ti.set_blocked_tasks ) in 
 if (priority>(!max)) then 
  max:=priority;
 i:=(!i)+1;
 done;
 !max
end
;;
(************************** Priority System **********************)
let priority_system_t lbuffers=
if(lbuffers=[]) then 
0.0
else
begin
let max=ref min_float  in 
let i= ref 0 in 
while (!i< (List.length lbuffers)) do 
 let priority=(List.nth lbuffers !i).priority_buf in
 if(priority> (!max)) then 
  max:=priority ;
  i:=(!i)+1;
done;
!max;
end;;

(************* Supprimer un élément**************)
let rec delete elem = function
  | [] -> []
  | x :: l -> 
      if elem=x then l else  x :: delete elem l;;

(***************************)
let rec insert elem = function
  | [] -> [elem]
  | x :: l -> 
      if elem < x then elem :: x :: l else if elem > x then x :: insert elem l else x :: l;;
(*
let rec insertBuffer elem = function
  | [] -> [elem]
  | x :: l -> 
      if elem < x then elem :: x :: l else if elem > x then x :: insertBuffer elem l else x :: l;;*)

(***************************)
let rec sort= function
  | [] -> []
  | x :: l -> insert x (sort l);;

(********************** Metier ********************)
let update_metier r_min met t ltask indice_selected_task t_1 =
(*Printf.printf "Test \n";*)
 if (t=r_min) then 
 {tasks_currently_used_buffers=[];buffer_curently_used_t=[];priority_system_t=0.0}
(*else
{tasks_currently_used_buffers=met.tasks_currently_used_buffers;buffer_curently_used_t=met.buffer_curently_used_t;priority_system_t=met.priority_system_t}*)
else
begin
 let setTasks = ref [] in (*met.tasks_currently_used_buffers in*)
 let i=ref 0 in
 while (!i<(List.length (met.tasks_currently_used_buffers))) do
  let ta= ref (List.nth (met.tasks_currently_used_buffers) !i) in
     (*Printf.printf " Av t_1=%d t=%d t%d.ci=%d\n" t_1 t (!ta).id (!ta).ci_t;*)
     ta:= (List.nth ltask !ta.indice) ;
    (* Printf.printf "Ap t_1=%d t=%d t%d.ci=%d\n" t_1 t (!ta).id (!ta).ci_t;*)
   if (t_1+(!ta).ci_t>t) then 
      setTasks:= (insert !ta (!setTasks));
   (*  setTasks:=(delete ta !setTasks); *)
   i:=(!i)+1;
 done;

 if(indice_selected_task!=(-1)) then
  begin 
  (*Printf.printf "Test2 %d task%d\n" t indice_selected_task ;*)
   let ti=(List.nth ltask indice_selected_task) in
   if ((t_1+ti.ci_t)>t) then 
    setTasks:= (insert ti (!setTasks));
   (*Printf.printf "Test3 %d task%d\n" t indice_selected_task ;*)
  end;

 let buffers=ref [] in 
 i:= 0;
 while (!i<(List.length !setTasks)) do
  let ta= (List.nth !setTasks !i) in
  let lbuf=ref ta.lbuffer in
  let j= ref 0 in
  while (!j <List.length !lbuf) do
   buffers:= (insert (List.nth (!lbuf) !j) !buffers);
   j:=(!j)+1;  
  done; 
  i:=(!i)+1;
 done;
 (*Printf.printf "Test3 %d \n" t;*)
{tasks_currently_used_buffers=(!setTasks);buffer_curently_used_t=(!buffers);priority_system_t=(priority_system_t !buffers)}
end;;


(****************************************************************************************)
let rec gcd x y =
  if x < y then
    if x = 0 then y
    else gcd (y mod x) x
  else if x > y then
    gcd y x
  else x
;;
(****************************************************************************************)
let lcm x y = x / gcd x y * y;;


(******************************************** Priority buffers *)

(********************************* Interval Goossens *****************************************************)
let compute_interval ltask=

let ti=(List.nth  ltask 0) in
let r_min= ref (ti.firstActivation) in
let h= ref ti.period in
let r_max= ref (!r_min) in
let i= ref 1 in
while (!i < (List.length ltask)) do
   let ta = (List.nth  ltask !i) in
   if(ta.firstActivation<(!r_min)) then 
   r_min:=(ta.firstActivation);
   let trans= ref  ta.firstActivation in 
   while (!trans) < (!r_max) do 
    trans:=(!trans) + ta.period
   done;

   r_max:=(!trans);
   h:=(lcm (!h) ta.period);


Printf.printf " id=%d tran=%d perm=%d f-interval=%d\n" (!i+1) !trans !h ((!r_max)+(!h)) ;
   i:=(!i)+1
done;
(*Printf.printf " max %d= \n"((!r_max)+(!h)) ;*)
{r_min=(!r_min);f_interval=((!r_max)+(!h))} ;;


(***************************)
let schedulability_interval ltask f_interval =
let li= ref [] in 
let ta=ref (List.nth  ltask 0) in
let t= ref (!ta.firstActivation) in
while ((!t)<= f_interval) do
 li:=(!li)@[!t];
 t:=(!t)+(!ta).period; 
done;

for i=0 to (List.length ltask)-1 do
ta:= (List.nth  ltask i);
t:= (!ta.firstActivation);

while ((!t)<= f_interval) do

let exists_li x =
if (x= (!t)) then 
true
else
false in

if ((List.exists exists_li (!li))=false) then 
li:=(!li)@[!t];
t:=(!t)+(!ta).period; 
done;
done;
(sort !li);;

(**************************************
let pred_succ t l=
let i=ref 0 in
let find= ref false in
while ((!i)< (List.length l)) & (!find=false) do
if((List.nth l !i)=t) then 
find:=true;
i:=(!i)+1
done;

 (*Printf.printf " t= %d i=%d et av %d mil %d ap %d \n" t (!i-1) (List.nth l (!i-1)) (List.nth l (!i)) (List.nth l (!i+1));*)
if(!i-1=0) then
 {t_p=(List.nth l (!i-1));t_s=(List.nth l (!i))}
else
if((!i-1)=((List.length l)-1)) then
 {t_p=(List.nth l (!i-2));t_s=(List.nth l (!i-1))}
else
 {t_p=(List.nth l (!i-2));t_s=(List.nth l (!i))}
;;*)

(***************************)
let next_t li i=
(*if (i<(List.length) then *)
(*Printf.printf "test i=%d\n" i;
for j=0 to (List.length li)-1 do
Printf.printf "%d " (List.nth li j) ;
done;
Printf.printf "\n";*)
(List.nth li (i+1)) 
;;

(**************************** Interval Leung et Merill ***********************************************************)
(*
let compute_interval ltask=
let h= ref 1 in
let i= ref 0 in
let r_min= ref max_int in
let r_max= ref min_int in

while (!i < (List.length ltask)) do
  let ta= (List.nth  ltask !i) in
  if(ta.firstActivation<(!r_min)) then 
   r_min:=(ta.firstActivation);

  if(ta.firstActivation>(!r_max)) then 
   r_max:=(ta.firstActivation);

  h:=(lcm (!h) ta.period);
  i:=(!i)+1
done;
{r_min=(!r_min);f_interval=((!r_max)+2*(!h))} ;;*)


(***************************************************************************************)
let compute_ci_t  ti t  p =
let ut=((t-ti.firstActivation) mod ti.period) in (* je garde pour ti que les valeurs de c_i sur l'instance considérée *)
(* let ci= ref ti.ci_t in
Printf.printf "t=%d idSelectedTask(t)=%d idSelectedTask(t-1)=%d  t_1=%d ci_t=%d\n" t p.idSelectedTask_t p.idSelectedTask_t_1 p.t_1 ti.ci_t ;*)
if (ut=0) then 
 ti.wcet
else
if(p.idSelectedTask_t_1!=ti.id) then 
 ti.ci_t
else
if((p.idSelectedTask_t=ti.id) || (p.idSelectedTask_t!=ti.id) & (p.t_1+ti.ci_t<=t)) then 
  max 0 ((p.t_1+ti.ci_t)-t)
else
 (((p.t_1+ti.ci_t)-t)+ti.preemption_cost);;
   (*Printf.printf " Task%d est préempté à t=%d \n" ti.id t;*)
(*Printf.printf "\n";*)


(***************************************************************************************)
let compute_di_t ti t p=
let ut=((t-ti.firstActivation) mod ti.period) in (* je garde pour ti que les valeurs de d_i sur l'instance considérée *)
if (ut=0) then 
 ti.deadline
else
if(ti.di_t >0) then 
max 0 ((p.t_1+ti.di_t)-t)
else
0;;
(*Printf.printf "t=%d task%d d%d(t)=%d  \n" t ti.id ti.id ti.di_t.(ut);*)


(********************** Set of blocked task by ti *******************)
let blocked_task_ti  t ti id_selectedtask readyTasks p=
let ci=(compute_ci_t  ti t  p) in
if(ci=0) then 
[]
else
if(ti.id!=id_selectedtask) then 
ti.set_blocked_tasks
else
begin
(*if (ti.id=4) then
 Printf.printf "***************** Test blocjked \n";*)
 let setTask= ref [] in
 let i=ref 0 in
 while (!i<(List.length readyTasks)) do
  let ta= (List.nth readyTasks !i) in
 (* Printf.printf "***************** id=%d ci_t=%d \n" ta.id ta.ci_t;*)
  if(ti.priority<ta.priority)&((compute_ci_t  ta t  p)!=0) then 
    setTask:= insert ta !setTask ;
  i:=(!i)+1;
 done;
!setTask;
end;;






(***************************************************************************************)
let phi_t  p t ltask met=
if(t=22) then
Printf.printf "prio_system =%f \n" met.priority_system_t; 
let i= ref 0 in
if(met.buffer_curently_used_t=[]) then 
begin
 let pro= ref {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=p.idSelectedTask_t;idSelectedTask_t_1=p.idSelectedTask_t_1;list_t=p.list_t;t=p.t;t_1=p.t_1;next_t=p.next_t;selectedTask=p.selectedTask} in
 let find= ref false in
 while ((!i < ((List.length ltask))) & (!find=false)) do
  let ta= List.nth  ltask !i in
  let ut=((t-ta.firstActivation) mod ta.period) in
  if ((ta.firstActivation=t)||(ut=0))then 
   begin
     (*p.phi_t.(t)<-ta.id;*)
     find:= true ;
     i:=!i+1
   end  
  else
  if (t>ta.firstActivation) then
   begin  
     (*&(p.idSelectedTask_t=ta.id)*)
    (* Printf.printf "Test p.t_1=%d ta.ci_t=%d task%d t=%d \n" p.t ta.ci_t ta.id t;*)
    if ((((p.t+ta.ci_t)>t)))||(ta.ci_t>0 & (p.idSelectedTask_t!=ta.id)) then (* idSelectedTask_t est equivalent au idSelectedTask_t-1 a ce niveau*)
        find:= true;
    i:=!i+1;
   end
  else
   i:=!i+1;
  if ((!find)=true) then 
  begin 
   p.phi_t.(t)<-ta.id;
   let id_1=p.idSelectedTask_t in
   let time1=p.t in
   pro:= {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=ta.id;idSelectedTask_t_1=id_1;list_t=p.list_t;t=t;t_1=time1;next_t=p.next_t;selectedTask=ta};
  end 
 done;
 
 if ((!find)=true) then 
  !pro
 else
 begin
  let id_1=p.idSelectedTask_t in
  let time2=p.t in
  {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=0;idSelectedTask_t_1=id_1;list_t=p.list_t;t=t;t_1=time2;next_t=p.next_t;selectedTask=p.selectedTask};
 end
end
else
begin
 i:=0;
 let pro= ref   {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=p.idSelectedTask_t;idSelectedTask_t_1=p.idSelectedTask_t_1;list_t=p.list_t;t=p.t;t_1=p.t_1;next_t=p.next_t;selectedTask=p.selectedTask}   in
 let find= ref false in
 while ((!i < ((List.length ltask))) & (!find=false)) do
  let ta= List.nth  ltask !i in
  let p_t=priority_ti_t ta ta.set_blocked_tasks in
  let ut=((t-ta.firstActivation) mod ta.period) in
  if (((ta.firstActivation=t)||(ut=0))&(p_t>met.priority_system_t))then 
    begin
     (*p.phi_t.(t)<-ta.id;*)
     find:= true ;
     i:=!i+1
    end  
  else
  if (t>ta.firstActivation) then
   begin  
    let p_t=(priority_ti_t ta ta.set_blocked_tasks) in
   (*&(p.idSelectedTask_t=ta.id)*)
   (* printf.printf "Test p.t_1=%d ta.ci_t=%d task%d t=%d \n" p.t ta.ci_t ta.id t;*)
    if (((((p.t+ta.ci_t)>t)))||(ta.ci_t>0 & (p.idSelectedTask_t!=ta.id)))&(p_t>met.priority_system_t)  then (* idSelectedTask_t est equivalent au idSelectedTask_t-1 a ce niveau*)
      find:= true;
    i:=!i+1;
   end
  else
  i:=!i+1;
  if ((!find)=true) then 
  begin 
   p.phi_t.(t)<-ta.id;
   let id_1=p.idSelectedTask_t in
   let time1=p.t in
   pro:={idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=ta.id;idSelectedTask_t_1=id_1;list_t=p.list_t;t=t;t_1=time1;next_t=p.next_t;selectedTask=ta};
  end 
done;

if ((!find)=true) then 
 !pro
else
begin
  let i=ref 0 in
  let max= ref min_float in
  let ta=ref (List.nth met.tasks_currently_used_buffers 0) in
  while (!i< (List.length met.tasks_currently_used_buffers)) do
    let tl=(List.nth met.tasks_currently_used_buffers !i) in
    let prio= (priority_ti_t  tl tl.set_blocked_tasks) in
    if (prio> (!max)) then 
     begin
     ta:= (List.nth met.tasks_currently_used_buffers !i);
     max:=prio;
     i:=(!i)+1;
     end
    else
    i:=(!i)+1;
  done;

 let id_1=p.idSelectedTask_t in
 let time2=p.t in
 {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=(!ta).id;idSelectedTask_t_1=id_1;list_t=p.list_t;t=t;t_1=time2;next_t=p.next_t;selectedTask=(!ta)};
end
end
;;

(***************************Compute k_ij**********************)
let k_i_j period_i period_j =
let r= (period_j mod period_i) in 
let q=(period_j / period_i) in
if(r!=0) then 
q+1 
else
q;;

(*****************************************buffers**********************************************)
let rec bi_t ltask ta t_1 idSelectedTask_t_1 t=
 if(t<ta.firstActivation+ta.wcet) then 
{id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=0;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks} 
else
if (ta.lsucc=[]) then
begin
let search_pred=ref false in
 let j=ref 0 in
 while (!j<(List.length ta.lpred)) & (!search_pred=false) do
 let tp=(List.nth ltask  (List.nth ta.lpred !j).indice) in
 if ((tp.bi_t=0)&(idSelectedTask_t_1!=ta.id))then 
  search_pred:=true;
  j:=(!j)+1;
 done;

  if(!search_pred=true) then
   {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority= (ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=0;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks} 
  else
  if (idSelectedTask_t_1=ta.id)&((t_1+ta.ci_t<=t)) then
   begin
    (*Printf.printf "Test t=%d id=%d b_%d=%d\n" t ta.id ta.id (ta.bi_t+1);*)
    {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=(ta.bi_t+1);lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks};
   end 
  else
     {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=(ta.bi_t);lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks}
end 
else
begin
 let b_succ=ref true in
 let i=ref 0 in
 while (!i<(List.length ta.lsucc)) & (!b_succ=true) do
 let tj=(List.nth ltask  (List.nth ta.lsucc !i).indice) in
 let k_ij= k_i_j ta.period tj.period  in
 let k_ji= k_i_j tj.period ta.period  in 
(* Printf.printf "Test//// t=%d id=%d b_%d=%d\n" t tj.id tj.id (bi_t tj t_1 idSelectedTask_t_1 t).bi_t;*)
 let bk= ((bi_t ltask tj t_1 idSelectedTask_t_1 t).bi_t) in  
(*Printf.printf "Test//// t=%d Task%d b_%d=%d k_ji=%d  k_ij=%d  b_%d=%d \n" t tj.id tj.id bk k_ji k_ij ta.id ta.bi_t ;*)
 if ( (( ((ta.bi_t*k_ji)-(bk*k_ij))!=0) || (idSelectedTask_t_1=ta.id)) || (bk!=0) ) then 
  b_succ:=false ;
  i:=(!i)+1;
 done;
  if((!b_succ=true)) then    
    {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=    (ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=0;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks} 
  else
  begin
  if (idSelectedTask_t_1=ta.id)&((t_1+ta.ci_t<=t)) then
    {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=(ta.bi_t+1);lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks}
  else
     {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=ta.bi_t;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks}  
 end
end
;;

(**************************************************************************************||((cit.(ut)=0)&(dit.(ut)=0))   ||((0<cit.(ut))&(cit.(ut)=dit.(ut))&(p.phi_t(t)=(ta.id))) *)
let scheduling_test_t ltask readyTasks p t next_t met r_min =
let li=ref p.list_t in
let l=ref [] in
let i= ref 0 in
let next= ref next_t in
let schedulable= ref true in

let ne= ref next_t in 
if(p.idSelectedTask_t!=0) then 
     ne:=(t+(compute_ci_t p.selectedTask t p));
  if((p.idSelectedTask_t!=0) & (!ne<next_t)) then
        next:=(!ne);
  li:=(insert !next !li) ;
 (*Printf.printf "length=%d \n" (List.length ltask);*)
while ((!i < ((List.length ltask))) & (!schedulable=true)) do
 let ta=ref (List.nth  ltask !i) in
 (* Printf.printf "i=%i id=%d \n" !ta.id !i; *)
 let setTaskblocked= (blocked_task_ti  t !ta p.idSelectedTask_t readyTasks p) in

(*if((!ta).id=4) then 
Printf.printf "Blocked by task 4length=%d \n" (List.length setTaskblocked);
for l=0 to (List.length setTaskblocked)-1 do
Printf.printf "task%d bloks tasks%d \n" (!ta).id (List.nth setTaskblocked l).id;
done;
*)
let bi=ref (bi_t ltask !ta p.t_1 p.idSelectedTask_t_1 t).bi_t in
 if(t>=(!ta).firstActivation) then 
   begin
 (*Printf.printf "af %d %d et %d \n"t ta.firstActivation (t-ta.firstActivation);*)
  let cit=compute_ci_t !ta t p in
  let dit= compute_di_t !ta t p in  
(*if(t<15) then *)
(* Printf.printf "t=%d c%d(t)=%d d%d=%d phi(t)=%d t_1=%d next_t=%d idSelectedTask=%d c%d=%d\n" t (!ta).id cit (!ta).id dit p.idSelectedTask_t p.t_1 next_t p.idSelectedTask_t (!ta).id cit; *)
(*if(t<15) then *)
   Printf.printf "t=%d c%d(t)=%d d%d=%d phi(t)=%d t_1=%d next_t=%d idSelectedTask=%d c%d=%d \n" t (!ta).id cit (!ta).id dit p.idSelectedTask_t p.t_1 next_t p.idSelectedTask_t  (!ta).id cit;      
 (*if ((!ta).id=p.idSelectedTask_t) &((t+cit)<next_t) then 
       next:=(t+cit);*)

(* Printf.printf "next=%d t=%d id=%d\n" !next t !ta.id;*)
(*((cit<dit) ) ||((cit=0)&(dit=0))||((0<cit)&(cit=dit)&(p.idSelectedTask_t=(!ta).id))  
((p.idSelectedTask_t=(!ta).id)&(cit<=dit))||((p.idSelectedTask_t!=(!ta).id)&((cit<=dit))&((t+cit)<=next))
(((0<cit)&(cit<=dit)&(p.idSelectedTask_t!=(!ta).id) &(((!next-(!ta).firstActivation) mod !ta.period)!=0))) ||((cit=0)&(dit=0))||((0<cit)&(cit<=dit)&(p.idSelectedTask_t=(!ta).id))
*)
  if ((cit<=dit)&((p.idSelectedTask_t=(!ta).id)||(cit=0)||(((!next-(!ta).firstActivation) mod !ta.period)!=0))) then 
    begin
 ta:= {id=(!ta).id;firstActivation=(!ta).firstActivation;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=cit;di_t=dit;bi_t=(!bi);lpred=(!ta).lpred;lsucc=(!ta).lsucc;indice=(!ta).indice;priority_t=(priority_ti_t !ta setTaskblocked);lbuffer=(!ta).lbuffer;set_blocked_tasks=(setTaskblocked)} ;
    l:=(!l)@ [!ta];
    (*  Printf.printf "t=%d task%d priority_t=%f\n" t (!ta).id (!ta).priority_t;*)
    (* else
      if((!ta).id=p.idSelectedTask_t_1) then 
        bi:= (bi_t p !ta t).bi_t;*)
     end 
  else
  begin
   schedulable:=false;
    Printf.printf "task%d is not schedulable at t=%d\n" !ta.id t;
  end 
 end 
else
 l:=(!l) @[{id=(!ta).id;firstActivation=(!ta).firstActivation;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=(!ta).ci_t;di_t=(!ta).di_t;bi_t=(!bi);lpred=(!ta).lpred;lsucc=(!ta).lsucc;indice=(!ta).indice;priority_t=(!ta).priority_t;lbuffer=(!ta).lbuffer;set_blocked_tasks=(!ta).set_blocked_tasks}];

(* Printf.printf "t=%d task%d priority_t=%f\n" t (!ta).id (!ta).priority_t;*)
i:=!i+1;
(*Printf.printf "t=%d phi(t)=%d task%d c%d(t)=%d  d%d=%d \n" t p.phi_t.(t) ta.id ti.id ti.ci_t ti.id ti.di_t*)
done;

let idselec= ref 0 in
if(p.idSelectedTask_t=0) then 
  idselec:=(-1) 
else
idselec:=p.selectedTask.indice;

(*let lb=met.buffer_curently_used_t in
for i=0 to (List.length lb)-1 do
 let bi= (List.nth lb i) in
Printf.printf "Buffer idBuf=%d prio_b=%f priority_system=%f  next=%d et t=%d\n" bi.idBuf bi.priority_buf met.priority_system_t !next t;
done;
*)
let met_t=update_metier r_min met !next !l !idselec t in

{proc={idproc=p.idproc;phi_t=p.phi_t;schedulable=(!schedulable);idSelectedTask_t=p.idSelectedTask_t;idSelectedTask_t_1=p.idSelectedTask_t_1;list_t=(!li);t=p.t;t_1=p.t_1;next_t=(!next);selectedTask=p.selectedTask};ltask=(!l);met=met_t}
(*end*)
;;


(*********************************)
let set_of_ready_tasks_t p ltask t=
let k=ref 0 in
let readyTasks= ref [] in
while (!k<(List.length ltask)) do 
let ta=(List.nth ltask !k) in 
 (*Printf.printf "++t=%d b%d=%d c%d=%d \n" t ta.id (bi_t ta p.t p.idSelectedTask_t t).bi_t ta.id (ta.ci_t) ;*)
(*let b_i= (bi_t ltask ta p.t p.idSelectedTask_t t).bi_t in
Printf.printf "******** bi_%d=%d c%d=%d t_1=%d id_t_1=%d \n" ta.id b_i ta.id ta.ci_t p.t p.idSelectedTask_t;*)



 k:=(!k)+1;
if(t>=ta.firstActivation) then 
begin
 let b_succ=ref true in
 let i=ref 0 in
 
 while (!i<(List.length ta.lsucc)) & (!b_succ=true) do
  let tj=(List.nth ltask (List.nth ta.lsucc !i).indice) in
 
  let k_ij= k_i_j ta.period tj.period  in
  let k_ji= k_i_j tj.period ta.period  in 
 (*Printf.printf "ta.period=%d tj.period=%d k_ij=%d kji=%d \n" ta.period tj.period  k_ij k_ji;*)
  let bj=((bi_t ltask ta p.t p.idSelectedTask_t t).bi_t*k_ji)-(((bi_t ltask tj p.t p.idSelectedTask_t t).bi_t)*k_ij) in  (*mod k_ji*)
  (*Printf.printf "++++ t=%d b%d=%d c%d=%d \n" t ta.id (bi_t p ta t).bi_t ta.id (ta.ci_t) ;*)
  if (bj>=k_ij) then 
  b_succ:=false ;
 (* Printf.printf "Succ Task%d k_%d%d=%d k_%d%d=%d diff=%d b_pred=%b\n" ta.id tj.id ta.id k_ij ta.id tj.id  k_ji bj !b_succ;*)
  i:=(!i)+1;
 done;

 if(!b_succ=true) then 
 begin
  let b_pred= ref true in
  i:=0;

  while (!i<(List.length ta.lpred)) & (!b_pred=true) do
   let ti=(List.nth ltask  (List.nth ta.lpred !i).indice )in
 (*  if(t=8)then
 Printf.printf "idPred de Task%d est Task%d\n" ta.id ti.id;*)
   let k_ij= k_i_j ti.period ta.period   in
   let k_ji= k_i_j ta.period  ti.period  in
   let bk=((bi_t ltask ta p.t p.idSelectedTask_t t).bi_t) in  
   let bi=(((bi_t ltask ti p.t p.idSelectedTask_t t).bi_t)*k_ji)-((bk)*k_ij) in (*/k_ji*)
      
    (* Printf.printf "t=%d Verif diff=%d \n"t bi;*)
   if (bi<k_ij) then 
    b_pred:=false ;

 (* Printf.printf "Pred idTask=%d k_%d%d=%d k_%d%d=%d diff=%d b_succ=%b\n" ta.id ti.id ta.id k_ij ta.id ti.id  k_ji bi !b_pred;*)
   i:=(!i)+1;
  done;

  if (!b_pred=true) then 
   readyTasks:=(!readyTasks)@[ta]
 end
end

done;
!readyTasks;;

(***************************************************************************************)
(********************************* Schedulability Condition ****************************)
(***************************************************************************************)
let new_schedulability_condition ltask interval li =

let ph=ref (Array.create (interval.f_interval) 0) in
let p=ref {idproc=1;phi_t=(!ph);schedulable=true;idSelectedTask_t=0;idSelectedTask_t_1=0;list_t=li;t=0;t_1=0;next_t=0;selectedTask=(List.nth ltask 0)} in
let t=ref (List.nth li 0) in
(*if(interval.r_min=0) then 
  t:= 0
else
 t:= List.nth li 0);
let j=(!t) in*)
let r= ref {proc=(!p);ltask=ltask; met={tasks_currently_used_buffers=[];buffer_curently_used_t=[];priority_system_t=0.0}} in
let n= ref !t in

Printf.printf " interval [%d %d]\n"interval.r_min interval.f_interval;
let k=ref 0 in 

while(((!t) <(interval.f_interval) & ((!r).proc.schedulable=true)) )do 
Printf.printf "******************** A t=%d ***********************\n" !t ;
let readyTasks=(set_of_ready_tasks_t !p (!r).ltask !t) in
  if((!n)=(!t)) then 
  n:=next_t ((!r).proc.list_t) !k;
  p:=(phi_t (!r).proc !t readyTasks (!r).met);
(* Printf.printf "t=%d next=%d  \n" !t !n;
for i=0 to (List.length readyTasks) -1 do
let ta = List.nth readyTasks i in
Printf.printf "ready tasks id=%d b%d_t=%d \n" ta.id ta.id ta.bi_t;
done;*)
Printf.printf "\n";

  r := (scheduling_test_t (!r).ltask readyTasks (!p) !t) !n (!r).met interval.r_min ;




(*let endt= Unix.time() in 

if((endt-.start) != 0.0) then 
Printf.printf "t=%d, la durée d'execution de scheduling_test_t =%fs\n" !t (endt-.start);*)
if(!n=((!r).proc).next_t) then 
k:=(!k)+1;
t:=((!r).proc).next_t ;
Printf.printf "NEXT !k=%d !n=%d m_next=%d !t=%d \n"!k !n ((!r).proc).next_t !t;
done; 
(*Printf.printf "\n";*)
if (((!r).proc).schedulable=true) then 
begin
Printf.printf "Le système est ordonnançable \n";
Printf.printf "Taille=%d " (List.length ((!r).proc).list_t);
(*for i=j to (interval.f_interval-1) do
Printf.printf "%d" (!r).proc.phi_t.(i);
done;*)
end
else
Printf.printf "Le système est non ordonnançable !!!\n";
Printf.printf "\n";
((!r).proc).schedulable
;;


(********************** Parser fich ****************************)
let parse_fic_tasks nomfic preemption_cost =
let ltask=ref[] in
let load=ref 0.0 in
let i=ref 1 in
let op = open_in (nomfic) in
let line =  ref (input_line op) in
let tk={id=0;firstActivation=0;wcet=1;period=6;deadline=6;preemption_cost=0;priority=(1.0/. 6.0);ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=1;priority_t=(1.0/. 6.0);lbuffer=[];set_blocked_tasks=[]} in
(*let ltask_bis=ref[] in*)
let sep=(Str.split  (Str.regexp "=") !line) in
let tab_tasks= ref (Array.create (int_of_string (List.nth sep 1)) tk) in
let len=(List.nth sep 1) in
let line =  ref (input_line op) in
let verif=ref false in
try
while (!line != "")   do
 line := input_line op;
 (*Printf.printf "%s \n" !line ;*)
 let tache =  Str.split  (Str.regexp " ") !line in
if((List.nth tache 0).[0]!='i')&(!verif=false) then
begin
 (*Printf.printf "%st \n" (List.nth tache 0);*)
ltask:=(!ltask)@[{id=(!i);firstActivation=(int_of_string (List.nth tache 1));wcet=(int_of_string (List.nth tache 2));period=(int_of_string (List.nth tache 3));deadline=(int_of_string (List.nth tache 4));preemption_cost=preemption_cost ;priority=(1.0/. (float_of_string (List.nth tache 3)));ci_t=0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=(!i-1);priority_t=(1.0/. (float_of_string (List.nth tache 3)));lbuffer=[];set_blocked_tasks=[]}];
(* Printf.printf "%s i=%d\n" (List.nth tache 3) !i;*)

if((List.length !ltask)!=(int_of_string len)) then
load:=(!load)+.((float_of_string (List.nth tache 2))/.(float_of_string (List.nth tache 3)));

i:=(!i)+1;
end 
else
if((List.nth tache 0).[0]='i')then 
begin
verif:=true ;
i:=1;
end
else
if(!verif=true) then
 begin
  (*Printf.printf " Test i=%d\n" !i;*)
  (* 6:3 5|9 10*)
 let tache2 =  Str.split  (Str.regexp ":") !line in
 let id1= (int_of_string (List.nth tache2 0)) in
 let ld=Str.split  (Str.regexp "|") (List.nth tache2 1) in
 let lpred=ref [] in
 let lsucc=ref [] in
 let ta= (List.nth !ltask (id1-1)) in (* la tâche considéré*)

(***** Sucesseurs de la tâche id1 ******************)
 let ldep2=Str.split  (Str.regexp " ") (List.nth ld 1) in

  for i=0 to (List.length ldep2)-1 do
   if((List.nth ld 1).[0]!='_') then
    begin
     let id= (int_of_string (List.nth ldep2 i)) in
      let succ=(List.nth !ltask (id-1)) in
    (*let kij=(k_i_j ta.period succ.period in*)
     lsucc:=(!lsucc)@[succ];
   end

  done;


  let tasks_may_use_b=([ta]@(!lsucc)) in
  let lbuf= ref [{idBuf=id1;priority_buf=(priority_buffer tasks_may_use_b);setTasks_may_use_b=tasks_may_use_b}] in
(***** Predecesseurs de la tâche id1 ******************)
 let ldep1=Str.split  (Str.regexp " ") (List.nth ld 0) in

  for i=0 to (List.length ldep1)-1 do
   if((List.nth ld 0).[0]!='_') then
     begin  
      let id= (int_of_string (List.nth ldep1 i)) in
      let pred= !tab_tasks.(id-1) in
      lbuf:=(!lbuf)@[(List.nth pred.lbuffer 0)];
      lpred:=(!lpred)@[pred];
   end
 done;
!tab_tasks.(id1-1)<-{id=ta.id;firstActivation=ta.firstActivation;wcet=ta.wcet;period=ta.period;deadline=ta.deadline;preemption_cost=ta.preemption_cost;priority=ta.priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=ta.bi_t;lpred=(!lpred);lsucc=(!lsucc);indice=ta.indice;priority_t=ta.priority_t;lbuffer=(!lbuf);set_blocked_tasks=ta.set_blocked_tasks};
 i:=(!i)+1;
 end
done;
({litasks=(Array.to_list !tab_tasks);load=(!load)});
 (*(Array.to_list !tab_tasks);
 (!ltask_bis);*)
with End_of_file -> close_in op ;
(*End_of_file|  -> close_in op;*)
({litasks=(Array.to_list !tab_tasks);load=(!load)});
;;
  (*(Array.to_list !tab_tasks);;*)
(*close_in op;*)
 (*!ltask_bis;;*)


(*
  ltask:=(!ltask)@[{id=(!i);firstActivation=(int_of_string (List.nth tache 1));wcet=(int_of_string (List.nth tache 2));period=(int_of_string (List.nth tache 3));deadline=(int_of_string (List.nth tache 4));preemption_cost=preemption_cost ;priority=(1.0/. (float_of_string (List.nth tache 3)));ci_t=0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=(!i-1);priority_t=(1.0/. (float_of_string (List.nth tache 3)));lbuffer=[];set_blocked_tasks=[]}];*)

(***************************************************************************************)
(******************************************** MAIN ****************************)
(***************************************************************************************)


let main =
let nomfichier= "/home/falou/simulations/tasks/" in
(*let fic_result_success= "/home/ROCQ/aoste/fndoye/simulations/result/success/succesratio_oplus_with_preemp_cost.ml" in*)
let fic_result_success= "/home/falou/simulations/result/data_synchro_mono_pro/succesratio_oplus_without_preemp_cost.ml" in
let preemption_cost=0 in
let oc=open_out fic_result_success in
for l=1 to 10 do
let moy_load=ref 0.0 in
let numsuccess=ref 0 in
let nomf=(nomfichier)^"SysTasks"^(string_of_int l)^"/" in 
 let numT=ref 0 in
for k=1 to 12 do 
(*let nomfic=(nomfichier)^(string_of_int k)^".ml" in*)
let fic=nomf^"setOfTask"^(string_of_int k)^".ml" in
let r_parse=(parse_fic_tasks fic preemption_cost) in
moy_load:=(!moy_load)+.(r_parse.load);
(*
Printf.printf "Listes des tâches :\n";
 for l=0 to (List.length r_parse.ltasks)-1 do
  let ti = (List.nth r_parse.ltasks l) in
  Printf.printf "id=%d r=%d C=%d T=%d D=%d\n" ti.id ti.firstActivation ti.wcet ti.period ti.deadline;
 done;
*)
(*
for i=0 to (List.length li)-1 do
Printf.printf "%d " (List.nth li i) ;
done;
Printf.printf "\n";*)

let interval= compute_interval r_parse.litasks in
let li=schedulability_interval r_parse.litasks interval.f_interval in

let startTime= Unix.time() in
let schedulable=new_schedulability_condition r_parse.litasks interval li in
let endtTime= Unix.time() in 
Printf.printf "Durée d'execution de oplusbis =%fs\n" (endtTime-.startTime);
if(schedulable=true)then
 numsuccess:=(!numsuccess)+1;
numT:=k;
done;
Printf.printf "Taux de succès =%d/12 \n" !numsuccess;
  Printf.fprintf oc "%f %f\n" (!moy_load/. (float_of_int !numT)) ((float_of_int !numsuccess)/.(float_of_int !numT));
done;
close_out oc;
 ;;




(*
let ltask=[!t_2;!t_1;!t_5;!t_3;!t_4] in(*;t_4;t_5;t_6;t_7;t_8] in*)
let interval= compute_interval ltask in
let li=schedulability_interval ltask interval.f_interval in

for i=0 to (List.length li)-1 do
Printf.printf "%d " (List.nth li i) ;
done;

let startTime= Unix.time() in
new_schedulability_condition ltask interval li;
let endtTime= Unix.time() in 
Printf.printf "Durée d'execution de oplusbis =%fs\n" (endtTime-.startTime);
 
(*Printf.printf "Test buffer 3 =%f\n"  (priority_buffer [!t_3;!t_4;!t_5]);*)*)





