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
 mutable firstActivation_2 :int;
 wcet : int;
 period: int;
 deadline: int;
 deadline_2: int;
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
 mutable set_blocked_tasks : task list;
 mutable idpro : int;
 mutable ltime_data_succ: lTime_data_succ array;
}
and 
lTime_data_succ=
{mutable idTask:int;
 mutable t_read_data:int}
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

type lresult_mono_proc=
{mutable lr : result array;
 mutable ltasks :  task list;
 mutable sched : bool;
 mutable list_t : int list;
 mutable latence : int;
 mutable t_begin : int;
}

type result_multi=
{mutable lresult: lresult_mono_proc;
 mutable ischedulable : bool;
 mutable latence_tasks: int;
}

type task_found=
{ta : task;
firstAct: int;
trouve : bool;
idP : int} 



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
      if elem < x then elem :: x :: l else if elem > x then x :: insert elem l else x ::l;;


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
let update_metier r_min met t ltask indice_selected_task t_1 lresult=
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
     (*lresult.lr.()*)

     ta:= (List.nth ltask !ta.indice) ;
   (*  Printf.printf " Test 4 i=%d \n" !i;*)
    
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

(*(********************************* Interval Goossens *****************************************************)
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


(*Printf.printf " id=%d tran=%d perm=%d f-interval=%d\n" (!i+1) !trans !h ((!r_max)+(!h)) ;*)
   i:=(!i)+1
done;
(*Printf.printf " max %d= \n"((!r_max)+(!h)) ;*)
{r_min=(!r_min);f_interval=((!r_max)+(!h))} ;;*)

(********************************* Interval  *****************************************************)
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

  if(ta.firstActivation>(!r_max)) then 
    r_max:=ta.firstActivation;
   (*let trans= ref  ta.firstActivation in 
   while (!trans) < (!r_max) do 
    trans:=(!trans) + ta.period
   done;
   r_max:=(!trans);
 *)
  
   h:=(lcm (!h) ta.period);


(*Printf.printf " id=%d tran=%d perm=%d f-interval=%d\n" (!i+1) !trans !h ((!r_max)+(!h)) ;*)
   i:=(!i)+1
done;
Printf.printf "r_min=%d r_max=%d h_n=%d tc+H_n=%d\n"!r_min !r_max !h ((!r_max)+(2*(!h)));
(*Printf.printf " max %d= \n"((!r_max)+(!h)) ; {r_min=(!r_min);f_interval=((!r_max)+(!h))} ;;*)
{r_min=(!r_min);f_interval=((!r_max)+(2*(!h)))} ;;


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
(*if(t=22) then
Printf.printf "prio_system =%f \n" met.priority_system_t; *)
let i= ref 0 in
if(met.buffer_curently_used_t=[]) then 
begin
 let pro= ref {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=p.idSelectedTask_t;idSelectedTask_t_1=p.idSelectedTask_t_1;t=p.t;t_1=p.t_1;next_t=p.next_t;selectedTask=p.selectedTask} in
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
   pro:= {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=ta.id;idSelectedTask_t_1=id_1;t=t;t_1=time1;next_t=p.next_t;selectedTask=ta};
  end 
 done;
 
 if ((!find)=true) then 
  !pro
 else
 begin
  let id_1=p.idSelectedTask_t in
  let time2=p.t in {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=0;idSelectedTask_t_1=id_1;t=t;t_1=time2;next_t=p.next_t;selectedTask=p.selectedTask};
 end
end
else
begin
 i:=0;
 let pro= ref   {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=p.idSelectedTask_t;idSelectedTask_t_1=p.idSelectedTask_t_1;t=p.t;t_1=p.t_1;next_t=p.next_t;selectedTask=p.selectedTask}   in
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
   pro:={idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=ta.id;idSelectedTask_t_1=id_1;t=t;t_1=time1;next_t=p.next_t;selectedTask=ta};
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
 {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=(!ta).id;idSelectedTask_t_1=id_1;t=t;t_1=time2;next_t=p.next_t;selectedTask=(!ta)};
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

(*************** find **********)
let  find_task_list ta l = 
let vbool=ref false in
let i=ref 0 in
let re=ref {ta={id=0;firstActivation=0;firstActivation_2=0;wcet=1;period=6;deadline=6;deadline_2=6;preemption_cost=0;priority=(1.0/. 6.0);ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=00;priority_t=(1.0/. 6.0);lbuffer=[];set_blocked_tasks=[];idpro=00;ltime_data_succ=[|{idTask=3;t_read_data=12}|]};firstAct=0;trouve=false;idP=0} in
while (!i<List.length l) &(!vbool=false) do
 let ti=(List.nth l !i) in 
 if(ti.id=ta.id) then 
 begin
 vbool:=true;
 re:={ta=ti;firstAct=ti.firstActivation_2;trouve=true;idP=ti.idpro};
 i:=(!i)+1;
 end
else
 i:=(!i)+1;
done; 
!re ;;


(***************************************** buffers**********************************************)
let bi_t ltask ta t_1 idSelectedTask_t_1 t tproc= (*rec*)
 if(t<ta.firstActivation+ta.wcet) then 
{id=(ta).id;firstActivation=(ta).firstActivation;firstActivation_2=ta.firstActivation_2;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;deadline_2=ta.deadline_2;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=0;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro;ltime_data_succ=ta.ltime_data_succ} 
else
(*if (ta.lsucc=[]) then
begin
let search_pred=ref false in
 let j=ref 0 in
 while (!j<(List.length ta.lpred)) & (!search_pred=false) do
 let ltask1= (tproc.((List.nth ta.lpred !j).idpro-1)).ltask in 
 let tp=(List.nth ltask1  (List.nth ta.lpred !j).indice) in
 if ((tp.bi_t=0)&(idSelectedTask_t_1!=ta.id))then 
  search_pred:=true;
  j:=(!j)+1;
 done;

  if(!search_pred=true) then
   {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority= (ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=0;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro} 
  else
  if (idSelectedTask_t_1=ta.id)&((t_1+ta.ci_t<=t)) then
   begin
    (*Printf.printf "Test t=%d id=%d b_%d=%d\n" t ta.id ta.id (ta.bi_t+1);*)
    {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=(ta.bi_t+1);lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro};
   end 
  else
     {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=(ta.bi_t);lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro}
end 
else
begin
 let b_succ=ref true in
 let i=ref 0 in
 while (!i<(List.length ta.lsucc)) & (!b_succ=true) do
  let tsucc=(List.nth ta.lsucc !i) in
  let ltask2= (tproc.(tsucc.idpro-1)).ltask in
  let tj=(List.nth ltask2 tsucc.indice) in
  let k_ij= k_i_j ta.period tj.period  in
  let k_ji= k_i_j tj.period ta.period  in 
(* Printf.printf "Test//// t=%d id=%d b_%d=%d\n" t tj.id tj.id (bi_t tj t_1 idSelectedTask_t_1 t).bi_t;*)
 let bk= ((bi_t ltask2 tj t_1 idSelectedTask_t_1 t tproc).bi_t) in  
(*Printf.printf "Test//// t=%d Task%d b_%d=%d k_ji=%d  k_ij=%d  b_%d=%d \n" t tj.id tj.id bk k_ji k_ij ta.id ta.bi_t ;*)
 if ( (( ((ta.bi_t*k_ji)-(bk*k_ij))!=0)||(idSelectedTask_t_1=ta.id)) || (bk!=0) ) then 
  b_succ:=false ;
  i:=(!i)+1;
 done;
  if((!b_succ=true)) then    
    {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=    (ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=0;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro} 
  else
  begin*)
  if (idSelectedTask_t_1=ta.id)&((t_1+ta.ci_t<=t)) then
    {id=(ta).id;firstActivation=(ta).firstActivation;firstActivation_2=ta.firstActivation_2;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;deadline_2=ta.deadline_2;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=(ta.bi_t+1);lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro;ltime_data_succ=ta.ltime_data_succ}
  else
     {id=(ta).id;firstActivation=(ta).firstActivation;firstActivation_2=ta.firstActivation_2;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;deadline_2=ta.deadline_2;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=ta.bi_t;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro;ltime_data_succ=ta.ltime_data_succ}  
 
(*end
end*)
;;

(**************************************************************************************||((cit.(ut)=0)&(dit.(ut)=0))   ||((0<cit.(ut))&(cit.(ut)=dit.(ut))&(p.phi_t(t)=(ta.id))) *)
let scheduling_test_t ltask readyTasks p t next_t met r_min lresult idpro max_interval ltasks costCom input output nbin nbout l_tinput l_toutput loutput ind=
let li=ref lresult.list_t in
let l=ref [] in
let i= ref 0 in
let next= ref next_t in
(*let t_begin=ref lresult.t_begin  in
let latence= ref lresult.latence in*)
let schedulable= ref true in
(*let nbp=ref 0 in*)
(*Printf.printf "t=%d et next_t=%d \n" t next_t;*)
let ne= ref next_t in 
let c_1=compute_ci_t p.selectedTask t p in
if(p.idSelectedTask_t!=0) then 
     ne:=(t+(c_1));
  if((p.idSelectedTask_t!=0) & (!ne<next_t))&(c_1>0) then
        next:=(!ne);
  li:=(insert !next !li) ;
 (* Printf.printf "Vrai next=%d \n" !next;*)

(*let min_t= ref max_int in*)
(* Printf.printf "length=%d \n" (List.length ltask);*)

while ((!i < ((List.length ltask))) & (!schedulable=true)) do
 let ta=ref (List.nth  ltask !i) in
 let bi=ref (bi_t ltask !ta p.t_1 p.idSelectedTask_t_1 t lresult.lr).bi_t in
 (* Printf.printf "t=%d ta%d bi=%d\n" t (!ta.id) !bi ;*)
 let ltime_data_s= ref (!ta).ltime_data_succ in


if(!ta.lpred=[])&(p.idSelectedTask_t=(!ta).id)then
begin
let b_succ=ref true in
 let ind_succ=ref 0 in
 while (!ind_succ<(List.length !ta.lsucc)) & (!b_succ=true) do
  let re= (find_task_list (List.nth !ta.lsucc !ind_succ) ltasks) in
  let ltas=lresult.lr.((re.ta).idpro-1).ltask in
  let tj_suc=(find_task_list re.ta ltas).ta in (* (List.nth ltask1 (re.ta).indice) in*)
  let mk_ij= k_i_j !ta.period tj_suc.period  in
  let mk_ji= k_i_j tj_suc.period !ta.period  in 
  let pr=lresult.lr.((re.ta).idpro-1) in 
  let bsucc=ref 0 in
  if(((re.ta).idpro-1)<ind) then 
   bsucc:=(((!bi)*mk_ji)-((tj_suc.bi_t)*mk_ij))  (*(bi_t ltas tj_suc p.t_1 pr.proc.idSelectedTask_t_1 t lresult.lr)   mod k_ji*)
   else
   bsucc:=(((!bi)*mk_ji)-(((bi_t ltas tj_suc p.t_1 pr.proc.idSelectedTask_t t lresult.lr).bi_t)*mk_ij)) ;
  if (!bsucc!=0) then 
  b_succ:=false ;
  ind_succ:=(!ind_succ)+1;
 done;

 (*  Printf.printf "++++++++++++  Test b_succ=%b\n"  !b_succ;*)
if(!nbin=0)&(!b_succ=true)then 
l_tinput:=(insert (((t-(!ta).firstActivation)/(!ta).period)*(!ta.period)) !l_tinput);
if(!b_succ=true)then 
nbin:=(!nbin)+1;

if(!nbin=input) then
nbin:=0;
end
else
nbin:=(!nbin);



if (p.idSelectedTask_t_1=(!ta).id) & (p.t_1+(!ta).ci_t<=t) then 
 begin
let test=ref 0 in
(**** ****)
 if(!ta.lsucc=[]) then 
  begin
  let b_pred= ref true in
  let ind_pred=ref 0 in
  while (!ind_pred<(List.length !ta.lpred)) & (!b_pred=true) do
   let re= (find_task_list (List.nth !ta.lpred !ind_pred) ltasks) in
   let ltask2=lresult.lr.((re.ta).idpro-1).ltask in 
   let ti=(find_task_list re.ta ltask2).ta in   (*(List.nth ltask1  (re.ta).indice )in*)
   let nk_ij= k_i_j ti.period !ta.period   in
   let nk_ji= k_i_j !ta.period  ti.period  in
   let b=ref 0 in
   let tdata= ref  (max_interval+1)in 
   let ln=ref 0 in
   let long= Array.length ti.ltime_data_succ in
   let vbool= ref false in 
  if(long=0) then
    vbool:=true;

  while (!ln<long)&(!vbool=false) do
   if ((ti.ltime_data_succ.(!ln)).idTask=(!ta).id) then 
    begin
    tdata:=((ti.ltime_data_succ.(!ln)).t_read_data) ;
    vbool:=true;
    ln:=(!ln)+1
    end
    else
   ln:=(!ln)+1;
  done;

 if(!ta.idpro=ti.idpro)||((!ta.idpro!=ti.idpro)&(t>=(!tdata))) then 
   begin 
    let pr=lresult.lr.((re.ta).idpro-1) in 
       if(((re.ta).idpro-1)<ind) then 
       begin
       test:=((bi_t ltask ti p.t_1 pr.proc.idSelectedTask_t_1 t lresult.lr).bi_t);
       b:=((ti.bi_t)*nk_ji)-((!bi)*nk_ij) (*(bi_t ltask ti p.t_1 pr.proc.idSelectedTask_t_1 t lresult.lr)*)
       end 
       else
       b:=(((bi_t ltask ti p.t_1 pr.proc.idSelectedTask_t t lresult.lr).bi_t)*nk_ji)-((!bi)*nk_ij) ;
    



        if(((re.ta).idpro-1)>=ind) then 
       test:=((bi_t ltask ti p.t_1 pr.proc.idSelectedTask_t t lresult.lr).bi_t);
(*
   if(!ta.id=5) then
    test:=(!b);*)
(*
   if(!ta.id=4)then
   Printf.printf "////// Test p.t_1=%d pr.proc.idSelectedTask_t_1=%d \n" p.t_1 !test;*)

    if (!b!=0)then 
      b_pred:=false ;
  end
  else
  b_pred:=false ;
   ind_pred:=(!ind_pred)+1;
 done;  

(*   Printf.printf "////// ta.id=%d b_pred=%b  nbout=%d b=%d bi=%d////////\n"!ta.id !b_pred !nbout !test !bi;
&(!b_pred=true)    if((t-lresult.t_begin)>(!latence))&(!b_pred=true)&(!bi<=1) then  *)
    if(!b_pred=true)&(((find_task_list !ta !loutput).ta).id!=(!ta).id) then
     begin
       nbout:=(!nbout)+1;
       (*if(!ta.id=5)then
       Printf.printf "////// Test  nbout=%d ////////\n" !nbout;*)
       loutput:=(!loutput)@[!ta]
     end 
  else
   nbout:=(!nbout); 

    if(!nbout=output)&(!b_pred=true)then
     begin
       l_toutput:=(insert t !l_toutput); (*(((t-(!ta).firstActivation)/(!ta).period)*(!ta.period))*)
       nbout:=0;
      loutput:=[];
     end
   else
   nbout:=(!nbout);
 end
  else
   nbout:=(!nbout); 

(**** ****)

   let j= ref 0 in 
   while (!j<(List.length (!ta).lsucc)) do
    let re= (find_task_list (List.nth !ta.lsucc !j) ltasks) in
    let ltask1=(lresult.lr).((re.ta).idpro-1).ltask in 
    let tj=(find_task_list re.ta ltask1).ta in
    let k_ij= k_i_j (!ta).period tj.period  in
    let k_ji= k_i_j tj.period (!ta).period  in 
    let pr=lresult.lr.((re.ta).idpro-1) in 
    let ndata= ref 0 in 
     if(((re.ta).idpro-1)<ind) then 
       ndata:= (((!bi)*k_ji)-((tj.bi_t)*k_ij)) (*(bi_t ltask1 tj p.t_1 pr.proc.idSelectedTask_t_1 t (lresult.lr))*)
     else
    ndata:= (((!bi)*k_ji)-(((bi_t ltask1 tj p.t_1 pr.proc.idSelectedTask_t t (lresult.lr)).bi_t)*k_ij));
 
    if(!ndata=k_ij)||(((!ta).period>tj.period)&(!ndata=k_ji)) then
     begin    
       if(!ta.idpro=tj.idpro) then 
        !ltime_data_s.(!j)<-{idTask=tj.id;t_read_data=t}
       else
      begin
       !ltime_data_s.(!j)<-{idTask=tj.id;t_read_data=(t+costCom)};
      let net=(t+costCom) in (*(!ltime_data_s.(!j).t_read_data)*)
      if(!ta.idpro!=tj.idpro)&(costCom!=0) then  
        li:=(insert net !li);

      if(net<(!next))&(costCom!=0)  then
         next:=net;
 
      end
     end 
     else
     if(!ndata>k_ij) then 
      !ltime_data_s.(!j)<-{idTask=tj.id;t_read_data=((!ta).ltime_data_succ.(!j)).t_read_data}
     else
      !ltime_data_s.(!j)<-{idTask=tj.id;t_read_data= (max_interval+2)};

     j:=(!j)+1
   done;
 end
 else
ltime_data_s:=(!ta).ltime_data_succ;

(*Printf.printf "Test 4 idpro=%d \n" idpro ;*)

 let setTaskblocked= (blocked_task_ti  t !ta p.idSelectedTask_t readyTasks p) in
 if(t>=(!ta).firstActivation) then 
   begin

 (*Printf.printf "af %d %d et %d \n"t ta.firstActivation (t-ta.firstActivation);*)
  let cit=compute_ci_t !ta t p in
  let dit= compute_di_t !ta t p in  
(*if(t<15) then *)
(* Printf.printf "t=%d c%d(t)=%d d%d=%d phi(t)=%d t_1=%d next_t=%d idSelectedTask=%d c%d=%d\n" t (!ta).id cit (!ta).id dit p.idSelectedTask_t p.t_1 next_t p.idSelectedTask_t (!ta).id cit; *)

(*if ((!ta.id=p.idSelectedTask_t)||(p.idSelectedTask_t=0)) then*)
(*if ((!ta.id=10)&(t<1200)) then*)
   (*Printf.printf "t=%d c%d(t)=%d d%d=%d phi(t)=%d t_1=%d next_t=%d idSelectedTask=%d c%d=%d\n" t (!ta).id cit (!ta).id dit p.idSelectedTask_t p.t_1 !next p.idSelectedTask_t  (!ta).id cit ;   *)     
if ((cit<=dit)&((!ta.firstActivation<=t)||(p.idSelectedTask_t_1=(!ta).id)||(!ta.ci_t=0)|| (((t-(!ta).firstActivation) mod !ta.period)!=0)))  then (*||(((t-(!ta).firstActivation) mod !ta.period)!=0) )) *) 
    begin 
 ta:= {id=(!ta).id;firstActivation=(!ta).firstActivation;firstActivation_2=(!ta).firstActivation_2;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;deadline_2=(!ta).deadline_2;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=cit;di_t=dit;bi_t=(!bi);lpred=(!ta).lpred;lsucc=(!ta).lsucc;indice=(!ta).indice;priority_t=(priority_ti_t !ta setTaskblocked);lbuffer=(!ta).lbuffer;set_blocked_tasks=(setTaskblocked);idpro=(!ta).idpro;ltime_data_succ=(!ltime_data_s)} ;
    l:=(!l)@ [!ta];
     end 
  else
  begin
   schedulable:=false;
    Printf.printf "task%d is not schedulable at t=%d\n" !ta.id t;
  end 
 end 
else
 l:=(!l) @[{id=(!ta).id;firstActivation=(!ta).firstActivation;firstActivation_2=(!ta).firstActivation_2;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;deadline_2=(!ta).deadline_2;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=(!ta).ci_t;di_t=(!ta).di_t;bi_t=(!bi);lpred=(!ta).lpred;lsucc=(!ta).lsucc;indice=(!ta).indice;priority_t=(!ta).priority_t;lbuffer=(!ta).lbuffer;set_blocked_tasks=(!ta).set_blocked_tasks;idpro=(!ta).idpro;ltime_data_succ=(!ltime_data_s)}];

(* Printf.printf "t=%d task%d priority_t=%f\n" t (!ta).id (!ta).priority_t;*)
i:=!i+1;
(*Printf.printf "t=%d phi(t)=%d task%d c%d(t)=%d  d%d=%d \n" t p.phi_t.(t) ta.id ti.id ti.ci_t ti.id ti.di_t*)
done;

let idselec= ref 0 in
if(p.idSelectedTask_t=0) then 
  idselec:=(-1) 
else
idselec:=p.selectedTask.indice;
(*
let lb=met.buffer_curently_used_t in
for i=0 to (List.length lb)-1 do
 let bi= (List.nth lb i) in
Printf.printf "Buffer idBuf=%d prio_b=%f priority_system=%f  next=%d et t=%d\n" bi.idBuf bi.priority_buf met.priority_system_t !next t;
done;*)
if(!schedulable=false) then
l:=ltask;
let met_t=update_metier r_min met !next !l !idselec t lresult in

  (*  next:= min !next !min_t ;*)
lresult.lr.(idpro)<-{proc={idproc=p.idproc;phi_t=p.phi_t;schedulable=(!schedulable);idSelectedTask_t=p.idSelectedTask_t;idSelectedTask_t_1=p.idSelectedTask_t_1;t=p.t;t_1=p.t_1;next_t=(!next);selectedTask=p.selectedTask};ltask=(!l);met=met_t};

(*if(leng=(List.length lresult.ltasks))&(!latence>(lresult.latence)) then*)
{lr=lresult.lr;ltasks=ltasks;sched=(!schedulable);list_t=(!li);latence=lresult.latence;t_begin=lresult.t_begin}
(*else
{lr=lresult.lr;ltasks=ltasks;sched=(!schedulable);list_t=(!li);latence=(!latence);t_begin=lresult.t_begin}*)
(*end*)
;;


(*********************************)
let set_of_ready_tasks_t p ltask t tproc max_interval ltasks ind=
let k=ref 0 in 
let readyTasks= ref [] in
while (!k<(List.length ltask)) do 
let ta=(List.nth ltask !k) in 
(*Printf.printf "Test ta%d\n" ta.id ;*)
 (*Printf.printf "++t=%d b%d=%d c%d=%d \n" t ta.id (bi_t ta p.t p.idSelectedTask_t t).bi_t ta.id (ta.ci_t) ;*)
(*
let b_i= (bi_t ltask ta p.t p.idSelectedTask_t t tproc).bi_t in
Printf.printf "******** bi_%d=%d c%d=%d t_1=%d id_t_1=%d \n" ta.id b_i ta.id ta.ci_t p.t p.idSelectedTask_t;*)
 k:=(!k)+1;
if(t>=ta.firstActivation) then 
begin
 let b_succ=ref true in
 let i=ref 0 in

 while (!i<(List.length ta.lsucc)) & (!b_succ=true) do
  let re= (find_task_list (List.nth ta.lsucc !i) ltasks) in
  let ltask1=tproc.((re.ta).idpro-1).ltask in
  let tj=(find_task_list re.ta ltask1).ta in (* (List.nth ltask1 (re.ta).indice) in*)
   (*Printf.printf "Succ de ta.id=%d est tsucc=%d  proc_succ=%d\n"ta.id tj.id tj.idpro;*)
  let k_ij= k_i_j ta.period tj.period  in
  let k_ji= k_i_j tj.period ta.period  in 
 (*Printf.printf "ta.period=%d tj.period=%d k_ij=%d kji=%d \n" ta.period tj.period  k_ij k_ji;*)

    let pr=tproc.((re.ta).idpro-1) in
   let bj= ref 0 in
      if(((re.ta).idpro-1)<ind) then 
    bj:=(((bi_t ltask ta p.t p.idSelectedTask_t t tproc).bi_t*k_ji)-( tj.bi_t)*k_ij)  (*mod k_ji*)
    else
    bj:=(((bi_t ltask ta p.t p.idSelectedTask_t t tproc).bi_t*k_ji)-( ((bi_t ltask1 tj pr.proc.t pr.proc.idSelectedTask_t t tproc).bi_t)*k_ij)) ;
(*if(((re.ta).idpro-1)<ind) then 
  Printf.printf "------------ tj.id=%d pr.proc.t_1=%d    pr.proc.idSelectedTask_t_1=%d diff=%d bj=%d\n"tj.id pr.proc.t_1  pr.proc.idSelectedTask_t_1 !bj ((bi_t ltask1 tj pr.proc.t_1 pr.proc.idSelectedTask_t_1 t tproc).bi_t)
  else
Printf.printf "------------ tj.id=%d pr.proc.t_1=%d    pr.proc.idSelectedTask_t_1=%d diff=%d bj=%d\n"tj.id pr.proc.t  pr.proc.idSelectedTask_t !bj ((bi_t ltask1 tj pr.proc.t pr.proc.idSelectedTask_t t tproc).bi_t); *)

  (*Printf.printf "++++ t=%d b%d=%d c%d=%d \n" t ta.id (bi_t p ta t).bi_t ta.id (ta.ci_t) ;
if(ta.id=4) then 
   Printf.printf "++ succ ti.id=%d diff=%d ++ \n"tj.id bj;*)
  if (!bj>=k_ij) then 
  b_succ:=false ;
 (* Printf.printf "Succ Task%d k_%d%d=%d k_%d%d=%d diff=%d b_pred=%b\n" ta.id tj.id ta.id k_ij ta.id tj.id  k_ji bj !b_succ;*)
  i:=(!i)+1;
 done;



 if(!b_succ=true) then 
 begin
  let b_pred= ref true in
  i:=0;

  while (!i<(List.length ta.lpred)) & (!b_pred=true) do
   let re= (find_task_list (List.nth ta.lpred !i) ltasks) in

   let ltask1=tproc.((re.ta).idpro-1).ltask in 
  (* Printf.printf "PredTest51 ta.id=%d ta.indice=%d length_ltask1=%d  (re.ta)=%d (re.ta).indice=%d (re.ta).idpro=%d\n"ta.id ta.indice (List.length ltask1) (re.ta).id (re.ta).indice (re.ta).idpro ;*)
   let ti=(find_task_list re.ta ltask1).ta in (*(List.nth ltask1  (re.ta).indice )in*)
   (*     if(ta.id=4) then 
   Printf.printf " ******************** pred de ta.id=%d est ti.id=%d len=%d\n"ta.id ti.id (List.length ta.lpred);
   Printf.printf "PredTest6  ta.id=%d ta.indice=%d ti.id=%d ti.indice=%d ti.idpro=%d\n"ta.id ta.indice ti.id ti.indice ti.idpro; *)
   let k_ij= k_i_j ti.period ta.period   in
   let k_ji= k_i_j ta.period  ti.period  in
   let bi=ref 0 in
   let tdata= ref  (max_interval+1) in 
   let li=ref 0 in
   let long= Array.length ti.ltime_data_succ in
   let vbool= ref false in 

  if(long=0) then
    vbool:=true;

  while (!li < long) & (!vbool=false) do
   if ((ti.ltime_data_succ.(!li)).idTask=ta.id) then 
    begin
    tdata:=((ti.ltime_data_succ.(!li)).t_read_data) ;
    vbool:=true;
    li:=(!li)+1
    end
    else
   li:=(!li)+1;
  done;

 if(ta.idpro=ti.idpro)||((ta.idpro!=ti.idpro)&(t>=(!tdata))) then 
   begin     

    let pr=tproc.((re.ta).idpro-1) in
    let bk=((bi_t ltask ta p.t p.idSelectedTask_t t tproc).bi_t) in  
    let bl=ref 0 in 
     if(((re.ta).idpro-1)<ind) then 
       bl:=(ti.bi_t)
        else
       bl:=((bi_t ltask ti pr.proc.t pr.proc.idSelectedTask_t t tproc).bi_t);
       bi:=(!bl*k_ji)-((bk)*k_ij);
 (* if(ta.id=4) then 
   Printf.printf "++ pred ti.id=%d diff=%d  bk=%d   bpred=%d ++ \n"ti.id !bi bk ((bi_t ltask ti p.t p.idSelectedTask_t t tproc).bi_t);*)
    if (!bi<k_ij) then 
      b_pred:=false ;
  end
  else
  b_pred:=false ;

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

(********************* Multiprocessor scheduling ******************************)
let multi_proc_with_data_dependances lresult interval li costCom input output=
let schedulable=ref true in
let latence =ref 0 in
let t=ref (List.nth li 0) in
let n= ref !t in
let nbout=ref 0 in
let nbin=ref 0 in
let l_tinput=ref [] in
let l_toutput=ref [] in
let loutput =ref [] in
(*let l_tbegin=ref [] in
Printf.printf " interval [%d %d]\n"interval.r_min interval.f_interval;*)
let k=ref 0 in 
let lresul=ref lresult in
while((!t) <(interval.f_interval) & (!lresul.sched=true)) do 

let m_next= ref max_int in 
let ind =ref 0 in
  if((!n)=(!t)) then (*&(!k<((List.length (!lresul.list_t))-1)*)
   n:=next_t (!lresul.list_t) !k;
(*Printf.printf "******************** A t=%d *********************** k=%d n=%d\n" !t !k !n;*)

(*     k:=(!k)+1; 
 for i=0 to (List.length !lresul.list_t) -1 do
   Printf.printf " %d " (List.nth !lresul.list_t i);
 done;
  Printf.printf " \n" ;*)
 (*let ne= ref max_int *)
 while (!ind<(Array.length !lresul.lr))& (!lresul.sched=true) do
  let r= ref ((!lresul.lr).(!ind)) in
 (* Printf.printf "length ltask l=%d \n" (List.length !r.ltask) ;*)
 (* Printf.printf "****** Processeur %d\n" (!r).proc.idproc;*)

  let p=ref (!r).proc in

  let readyTasks=(set_of_ready_tasks_t !p  (!r).ltask !t !lresul.lr interval.f_interval !lresul.ltasks !ind) in

(*
Printf.printf "Ready tasks\n"; 
 for i=0 to (List.length readyTasks) -1 do
 let ta = List.nth readyTasks i in
 Printf.printf " *+*+*+*+*+*+* ready tasks id=%d b%d_t=%d \n" ta.id ta.id ta.bi_t;
 done;*)


 (* Printf.printf "nextt %d \n" !n ;*)
  p:=(phi_t (!r).proc !t readyTasks (!r).met);

 (* if(!p.idSelectedTask_t!=0) then
  l_tbegin:=(insert !p.idSelectedTask_t !l_tbegin);*)

 lresul:= (scheduling_test_t  (!r).ltask readyTasks (!p) !t !n  (!r).met interval.r_min !lresul !ind interval.f_interval !lresul.ltasks costCom input output nbin nbout l_tinput l_toutput loutput !ind);
 if(!lresul.latence>(!latence)) then
  latence:=(!lresul.latence);

 if (!m_next>((!lresul.lr).(!ind).proc).next_t) then 
 m_next:=((!lresul.lr).(!ind).proc).next_t;
 ind:=(!ind)+1;
done;
 (* Printf.printf "nextscjghqjk %d \n" (!m_next) ;*)
 (*if(!n=(!m_next))then *)
(*if(!n>=(!m_next))then *)
 k:=(!k)+1;
(*if(!m_next=(!t)) then
t:=(!n)
else*)

t:=(!m_next) 
(*else
t:=*)
(*Printf.printf "NEXT !k=%d !n=%d m_next=%d !t=%d \n"!k !n (!m_next) !t;*)
done; 

if (!lresul.sched=true) then 
schedulable:=true
else
 schedulable:=false;

if(!schedulable=true) then 
Printf.printf "Le système est ordonnançable \n"
else
Printf.printf "Le système est non ordonnançable !!!\n";
(*Printf.printf " ----- Latences -------- linput=%d loutput=%d ninput=%d noutput=%d \n" (List.length !l_tinput)  (List.length !l_toutput) input output;*)
latence :=min_int ;
for i=0 to (min ((List.length !l_toutput)-1) ((List.length !l_tinput)-1)) do
if(!latence<((List.nth !l_toutput i)-(List.nth !l_tinput i))) then
latence:=((List.nth !l_toutput i)-(List.nth !l_tinput i));
(*Printf.printf "cycle 1  debut=%d   fin=%d \n" (List.nth !l_tinput i) (List.nth !l_toutput i)*)
done;
{lresult=(!lresul);ischedulable=(!schedulable);latence_tasks=(!latence)};;

(*************************************** Parser le fichier de tâches ************************************)
let parse_fic_tasks nomfic preemption_cost =
let ltask=ref[] in
let load=ref 0.0 in
let i=ref 1 in
let op = open_in (nomfic) in
let line =  ref (input_line op) in
let tk={id=0;firstActivation=0;firstActivation_2=0;wcet=1;period=6;deadline=6;deadline_2=6;preemption_cost=0;priority=(1.0/. 6.0);ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=1;priority_t=(1.0/. 6.0);lbuffer=[];set_blocked_tasks=[];idpro=1;ltime_data_succ=[|{idTask=3;t_read_data=12}|]} in
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
  ltask:=(!ltask)@[{id=(!i);firstActivation= (int_of_string (List.nth tache 1));firstActivation_2=(int_of_string (List.nth tache 1));wcet=(int_of_string (List.nth tache 2));period=(int_of_string (List.nth tache 3));deadline=(int_of_string (List.nth tache 4));deadline_2=(int_of_string (List.nth tache 4));preemption_cost=preemption_cost ;priority=(1.0/. (float_of_string (List.nth tache 3)));ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=(!i-1);priority_t=(1.0/. (float_of_string (List.nth tache 3)));lbuffer=[];set_blocked_tasks=[];idpro=0;ltime_data_succ=[||]}];
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
 let ltime_data= ref (Array.create (List.length ldep2) {idTask=0;t_read_data=max_int}) in

  for i=0 to (List.length ldep2)-1 do
   if((List.nth ld 1).[0]!='_') then
    begin
     let id= (int_of_string (List.nth ldep2 i)) in
      let succ=(List.nth !ltask (id-1)) in
    (*let kij=(k_i_j ta.period succ.period in*)
      !ltime_data.(i)<-{idTask=succ.id;t_read_data=max_int};
     lsucc:=(!lsucc)@[succ];
   end
else
  ltime_data:=[||];
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
!tab_tasks.(id1-1)<-{id=ta.id;firstActivation=ta.firstActivation;firstActivation_2=ta.firstActivation_2;wcet=ta.wcet;period=ta.period;deadline=ta.deadline;deadline_2=ta.deadline_2;preemption_cost=ta.preemption_cost;priority=ta.priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=ta.bi_t;lpred=(!lpred);lsucc=(!lsucc);indice=ta.indice;priority_t=ta.priority_t;lbuffer=(!lbuf);set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro;ltime_data_succ=(!ltime_data)};
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


(********************* Partie allocation des tâches sur les processeurs ********************************)
(*******************************************************************************************************)




(**************** slack *******************)
let slack ti=
(ti.firstActivation+ti.deadline)-(ti.firstActivation_2+ti.wcet);;

(***************************)
let rec insert_w elem = function
  | [] -> [elem]
  | x :: l -> 
      if (slack elem) < (slack x) then elem :: x :: l else if (slack elem) > (slack elem) then x :: insert_w elem l else x ::elem::l;;

(*let rec insert_w elem = function
  | [] -> [elem]
  | x :: l -> 
      if elem.priority > x.priority  then elem::x:: l else if elem.priority < x.priority then x :: insert_w elem l else x ::elem::l;;*)


(************* w(t) *******)
let w_t ltask ti t=
 let sum=ref ti.wcet in
 let i= ref 0 in 

while (!i<((List.length ltask)-1)) do
 let ta=(List.nth ltask !i) in
 if(((t-ta.firstActivation)mod ta.period)=0) then 
  sum:=(!sum)+((t-ta.firstActivation)/ta.period)*ta.wcet 
 else
  sum:=(!sum)+(((t-ta.firstActivation)/ta.period)+1)*ta.wcet;
  i:=(!i)+1
done;
!sum;;

(******************  wrt *******************)
let wrt ltask ti=
 let wr= ref ti.wcet in
 (*while (!wr!=(w_t ltask ti !wr))  do
  wr:=(w_t ltask ti !wr);
 done ;*)
  !wr ;;

(*******************  setW************************************)
let setW ltask=
let w= ref [] in 
for i=0 to (List.length ltask)-1 do 
 let ta=(List.nth ltask i) in
 if(ta.lpred=[]) then 
  begin
  w:=(insert_w ta !w) ;
  (*Printf.printf " set_w id=%d period=%d len_w=%d \n" ta.id ta.period (List.length !w) ;*)
  end
done;

 (* Printf.printf "/ len_w=%d\n" (List.length !w);*)
 !w;;

(************* Supprimer une tâche**************)
let rec delete_task elem = function
  | [] -> []
  | x :: l -> 
      if elem.id=x.id then l else  x :: delete elem l;;

(******************updateW****************************)
let update_w w ti ltask l_sched_task=
(*Printf.printf " Pour t%d \n" ti.id;*)
let wb= ref (delete_task ti w) in

(*Printf.printf " 777 Après update W  : " ;
 for j=0 to (List.length !wb) -1 do
  let tj = List.nth !wb j in
  Printf.printf "%d " tj.id;
 done;
  Printf.printf "fin\n";*)
let i= ref 0 in
while (!i<(List.length ti.lsucc)) do
 let ta=(List.nth ltask (List.nth ti.lsucc !i).indice) in
 let trouve= ref false in
 let l=ref 0 in
  (*Printf.printf "********* j=%d ta ta%d lpred=%d \n" l ta.id (List.length ta.lpred);
  Printf.printf " je suis %d lsuc=%d \n" ta.id (List.length ta.lsucc);*)
 
  while(!l<(List.length ta.lpred))&(!trouve=false) do 
   let tk=ref (List.nth ltask (List.nth ta.lpred !l).indice) in

   (*Printf.printf "t%d<t%d \n" !tk.id ta.id  ;*)
   if((find_task_list !tk l_sched_task).trouve=false) then 
    trouve:=true;
   l:=(!l)+1;
  done;
  if((!trouve=false)&(ta.lpred!=[])) then 
   begin 
    wb:=(insert_w ta !wb);
   i:=(!i)+1
   end
   else
  i:=(!i)+1
done;

(*
Printf.printf "after update wb %d %d\n" (List.nth !wb 0).id  (List.length !wb);

(*Printf.printf " 8888 Après update W  : " ;*)

 for j=0 to (List.length !wb) -1 do
  let tj = List.nth !wb j in
  Printf.printf "%d " tj.id;
 done;
  Printf.printf "Fin \n";*)
!wb;; 

(********************* add tri *********************)
let add_tri_priority ltask ta=
let i= ref 0 in
let list_task=ref[] in
while(!i<(List.length ltask))&((List.nth ltask !i).period<=ta.period) do
list_task:=(!list_task)@[(List.nth ltask !i)];
i:=(!i)+1;
done;

list_task:=(!list_task)@[{id=(ta).id;firstActivation=(ta).firstActivation;firstActivation_2=(ta).firstActivation_2;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;deadline_2=(ta).deadline_2;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=(ta).ci_t;di_t=(ta).di_t;bi_t=(ta).bi_t;lpred=(ta).lpred;lsucc=(ta).lsucc;indice=(!i);priority_t=(ta).priority_t;lbuffer=(ta).lbuffer;set_blocked_tasks=(ta).set_blocked_tasks;idpro=(ta).idpro;ltime_data_succ=(ta).ltime_data_succ}];

let k=ref ((!i)+1) in 

while(!i<(List.length ltask)) do
let ti=(List.nth ltask !i) in 
list_task:=(!list_task)@[{id=ti.id;firstActivation=ti.firstActivation;firstActivation_2=ti.firstActivation_2;wcet=ti.wcet;period=ti.period;deadline=ti.deadline;deadline_2=ti.deadline_2;preemption_cost=ti.preemption_cost;priority=ti.priority;ci_t=ti.ci_t;di_t=ti.di_t;bi_t=ti.bi_t;lpred=ti.lpred;lsucc=ti.lsucc;indice=(!k);priority_t=ti.priority_t;lbuffer=ti.lbuffer;set_blocked_tasks=ti.set_blocked_tasks;idpro=ti.idpro;ltime_data_succ=ti.ltime_data_succ}];
i:=(!i)+1;
k:=(!k)+1;
done;
!list_task;;

(***************************)
let rec insert_task elem = function
  | [] -> [elem]
  | x :: l -> 
      if elem.period < x.period then elem :: x :: l else if elem.period > x.period then x :: insert_task  elem l else x ::elem:: l;;
(************************** Algorithme Exact de type Branch and Bound **************************************************************)
(*****************************************************************************************************************************)
let algo_exact ltask nbproc interval li costCom preemption_cost input output=
  let lsolution=ref [] in
  let list_task_scheduled =ref [] in
  let p_ini={idproc=0;phi_t=(Array.create (interval.f_interval) 0);schedulable=true;idSelectedTask_t=0;idSelectedTask_t_1=0;t=0;t_1=0;next_t=0;selectedTask={id=0;firstActivation=0;firstActivation_2=0;wcet=1;period=6;deadline=6;deadline_2=6;preemption_cost=0;priority=(1.0/. 6.0);ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=0;priority_t=(1.0/. 6.0);lbuffer=[];set_blocked_tasks=[];idpro=1;ltime_data_succ=[|{idTask=3;t_read_data=12}|]}} in
 
  let r_ini={proc=(p_ini);ltask=[]; met={tasks_currently_used_buffers=[];buffer_curently_used_t=[];priority_system_t=0.0}} in
  let lresult= ref ({lr=(Array.create nbproc r_ini );ltasks=[];sched=true;list_t=li;latence=0;t_begin=interval.r_min} )in

  for li=0 to (Array.length !lresult.lr)-1 do
    let p_ini_b={idproc=(li+1);phi_t=(Array.create (interval.f_interval) 0);schedulable=true;idSelectedTask_t=0;idSelectedTask_t_1=0;t=0;t_1=0;next_t=0;selectedTask={id=0;firstActivation=0;firstActivation_2=0;wcet=1;period=6;deadline=6;deadline_2=6;preemption_cost=0;priority=(1.0/. 6.0);ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=0;priority_t=(1.0/. 6.0);lbuffer=[];set_blocked_tasks=[];idpro=1;ltime_data_succ=[|{idTask=3;t_read_data=12}|]}} in

  let r_ini_b={proc=(p_ini_b);ltask=[]; met={tasks_currently_used_buffers=[];buffer_curently_used_t=[];priority_system_t=0.0}} in
  !lresult.lr.(li)<-r_ini_b;
  done;

  
  let i=ref 0 in 
  let w = ref (setW ltask) in
  let ph=(Array.create (interval.f_interval) 0) in 
  let ta=ref (List.nth !w 0) in

  ta:={id=(!ta).id;firstActivation=(!ta).firstActivation;firstActivation_2=(!ta).firstActivation;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;deadline_2=(!ta).deadline;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=(!ta).ci_t;di_t=(!ta).di_t;bi_t=(!ta).bi_t;lpred=(!ta).lpred;lsucc=(!ta).lsucc;indice=0;priority_t=(!ta).priority_t;lbuffer=(!ta).lbuffer;set_blocked_tasks=(!ta).set_blocked_tasks;idpro=1;ltime_data_succ=(!ta).ltime_data_succ};


  let p={idproc=1;phi_t=(ph);schedulable=true;idSelectedTask_t=0;idSelectedTask_t_1=0;t=0;t_1=0;next_t=0;selectedTask=(!ta)} in
  let r={proc=(p);ltask=[!ta]; met={tasks_currently_used_buffers=[];buffer_curently_used_t=[];priority_system_t=0.0}} in

  !lresult.lr.(!i)<-r;
  lresult:={lr=(!lresult.lr);ltasks=[!ta];sched=true;list_t=li;latence=0;t_begin=interval.r_min};
  w:= (update_w  !w !ta ltask  [!ta]);
  lsolution:=(!lsolution)@[!lresult];
  list_task_scheduled:=(!list_task_scheduled)@[!ta];
  i:=(!i+1);
let schedulable = ref true in
while ((!w!=[]) & ((!schedulable)=true)) do
  let ta = ref (List.nth !w 0) in
  schedulable:=false;
  let lsolui= ref [] in
  for j=0 to ((List.length !lsolution)-1)  do
   lresult:=(List.nth !lsolution j) ;
  
   let i= (List.length (!lresult.ltasks)) in
   let lp= ref 0 in 
   while (!lp<(i+1)) &(!lp<nbproc) do 
     let ltasks= ref (!lresult.ltasks)in
     (*let proc=(!lresult.lr.(!lp)) in
     let rmax=ref min_int in
     for l=0 to (List.length !ta.lpred)-1 do
       let pred= (List.nth ltask  (List.nth !ta.lpred l).indice) in
       let re=(find_task_list pred !ltasks) in
       let kij= (k_i_j pred.period !ta.period) in
       rmax:= max !rmax (re.firstAct+((kij-1)*pred.period)+(pred.wcet))
     done;

     let r_ta=(max !rmax !ta.firstActivation) in*)
     let tb= ref {id=(!ta).id;firstActivation=(!ta).firstActivation;firstActivation_2=(!ta).firstActivation_2;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;deadline_2=(!ta).deadline;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=(!ta).ci_t;di_t=(!ta).di_t;bi_t=(!ta).bi_t;lpred=(!ta).lpred;lsucc=(!ta).lsucc;indice=(!ta).indice;priority_t=(!ta).priority_t;lbuffer=(!ta).lbuffer;set_blocked_tasks=(!ta).set_blocked_tasks;idpro=(!lp+1);ltime_data_succ=(!ta).ltime_data_succ} in
    
   (*  if ((wrt proc.ltask (!ta))<=(!ta).deadline) then 
      begin   *)
       tb:={id=(!ta).id;firstActivation=(!ta).firstActivation;firstActivation_2=(!tb).firstActivation_2;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;deadline_2=(!tb).deadline_2;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=(!ta).ci_t;di_t=(!ta).di_t;bi_t=(!ta).bi_t;lpred=(!ta).lpred;lsucc=(!ta).lsucc;indice=((List.length ((!lresult.lr).(!lp)).ltask));priority_t=(!ta).priority_t;lbuffer=(!ta).lbuffer;set_blocked_tasks=(!ta).set_blocked_tasks;idpro=(!lp+1);ltime_data_succ=(!ta).ltime_data_succ};
       
        let solu=ref ({lr=(Array.create nbproc r_ini );ltasks=[];sched=true;list_t=li;latence=0;t_begin=interval.r_min} ) in
         for k= 0 to (Array.length !lresult.lr)-1 do
          (!solu.lr).(k)<-(!lresult.lr).(k);
         done;
 
        
        !solu.lr.(!lp)<-{proc=((!solu.lr).(!lp)).proc;ltask=(add_tri_priority  (((!solu.lr).(!lp)).ltask) !tb); met=((!solu.lr).(!lp)).met} ;
           
        ltasks:=(insert_task !tb !ltasks);
          (* if(!tb.id=4) then
           Printf.printf " -------tb=%d  tb.idproc=%d tb.indice=%d length_solu.ltask=%d ltasks.4=%d\n" !tb.id !tb.idpro !tb.indice (List.length !solu.lr.(!tb.idpro-1).ltask) (find_task_list !tb !ltasks).ta.idpro;*)
        solu:={lr=(!solu.lr);ltasks=(!ltasks);sched=true;list_t=li;latence=0;t_begin=interval.r_min};
        lsolui:=(!lsolui)@[!solu];
        schedulable:=true;
       lp:=(!lp)+1;
     (*end
     else
   lp:=(!lp)+1;*)
   done;

 done;
   lsolution:=(!lsolui);
   list_task_scheduled:=(!list_task_scheduled)@[!ta];
  i:=(!i+1);
   w:=(update_w !w !ta ltask !list_task_scheduled);
done; 

(*(List.length !lsolution)-1)*)

(*for ind=0 to (List.length !lsolution)-1 do
let lresult=(List.nth !lsolution ind) in
 Printf.printf " ------------------- Solution =%d  ---------------- \n" (ind+1);
for i=0 to (Array.length lresult.lr)-1 do 
 let pr= lresult.lr.(i) in
 Printf.printf " ++++++ Processeur %d  +++++++\n" (pr.proc).idproc;

 for j=0 to (List.length pr.ltask)-1 do
  let ta = List.nth pr.ltask j in
  Printf.printf "t%d indice=%d idpro=%d\n" ta.id ta.indice ta.idpro;
 done;
 Printf.printf "\n";
done;
 Printf.printf " --------------------------------- \n" ;
done;*)

 Printf.printf " --------------------------------- leng=%d\n" (List.length !lsolution);
let result=ref (multi_proc_with_data_dependances (List.nth !lsolution 0) interval li costCom input output) in

let ordo= ref false in 
let latence= ref max_int in
let taille =(List.length !lsolution) in
for ind=0  to (taille-1)  do
Printf.printf " ---- n_sol_restantes=%d\n" (taille-ind);
 let lresult=(List.nth !lsolution ind) in
 let result_multi_sched=(multi_proc_with_data_dependances lresult interval li costCom input output) in
 (* Printf.printf " ------------------- Solution numméro %d latence=%d---------------- \n" (ind+1) result_multi_sched.latence_tasks;*)
 (*  for i=0 to (Array.length lresult.lr)-1 do 
     let pr= lresult.lr.(i) in
     Printf.printf " ++++++ Processeur %d  +++++++\n" (pr.proc).idproc;

     for j=0 to (List.length pr.ltask)-1 do
     let ta = List.nth pr.ltask j in
     Printf.printf "t%d indice=%d idpro=%d\n" ta.id ta.indice ta.idpro;
     done;
     Printf.printf "\n";
 done;

*)
 if(result_multi_sched.ischedulable=true) then 
  begin 
    result:=result_multi_sched;
    ordo:=true;
    if(!latence>result_multi_sched.latence_tasks)  then 
     latence:=result_multi_sched.latence_tasks 
    else
     latence:=(!latence);
     result:=result_multi_sched;
     (*
     for i=0 to (Array.length lresult.lr)-1 do 
     let pr= lresult.lr.(i) in
     Printf.printf " ++++++ Processeur %d  +++++++\n" (pr.proc).idproc;

     for j=0 to (List.length pr.ltask)-1 do
     let ta = List.nth pr.ltask j in
     Printf.printf "t%d indice=%d idpro=%d\n" ta.id ta.indice ta.idpro;
     done;
     Printf.printf "\n";*)
  end 
   else
   latence:=(!latence);
done;
(*
if(!ordo=false) then
Printf.printf "Système non ordonnançable \n"
else
Printf.printf "Système ordonnançable latence=%d \n" !latence;*)
(*if(!result.ischedulable=true) then
Printf.printf "Test 1\n"
else
Printf.printf "Test 2\n";*)
(!result);;



(*************************** fin partie allocation des tâches *************************************)
(*************** find **********)
let  find_task_list_period_diff ta l = 
let vbool=ref false in
let i=ref 0 in
let re=ref {ta={id=0;firstActivation=0;firstActivation_2=0;wcet=1;period=6;deadline=6;deadline_2=6;preemption_cost=0;priority=(1.0/. 6.0);ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=0;priority_t=(1.0/. 6.0);lbuffer=[];set_blocked_tasks=[];idpro=00;ltime_data_succ=[|{idTask=3;t_read_data=12}|]};firstAct=0;trouve=false;idP=0} in
while (!i<List.length l) &(!vbool=false) do
 let ti=(List.nth l !i) in 
 if(ti.period=ta.period) then 
 begin
 vbool:=true;
 re:={ta=ti;firstAct=ti.firstActivation_2;trouve=true;idP=ti.idpro};
 i:=(!i)+1;
 end
else
 i:=(!i)+1;
done; 
!re ;;

(*************************** fin partie allocation des tâches *************************************)
(*************** find **********)
let  find_task_list_period_diff ta l = 
let vbool=ref false in
let i=ref 0 in
let re=ref {ta={id=0;firstActivation=0;firstActivation_2=0;wcet=1;period=6;deadline=6;deadline_2=6;preemption_cost=0;priority=(1.0/. 6.0);ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=00;priority_t=(1.0/. 6.0);lbuffer=[];set_blocked_tasks=[];idpro=00;ltime_data_succ=[|{idTask=3;t_read_data=12}|]};firstAct=0;trouve=false;idP=0} in
while (!i<List.length l) &(!vbool=false) do
 let ti=(List.nth l !i) in 
 if(ti.period=ta.period) then 
 begin
 vbool:=true;
 re:={ta=ti;firstAct=ti.firstActivation_2;trouve=true;idP=ti.idpro};
 i:=(!i)+1;
 end
else
 i:=(!i)+1;
done; 
!re ;;

(*************************)
type struct_result_simulation=
{ ab : float;
 ord : float;
}
(***************************)
let rec insert_result el = function
  | [] -> [el]
  | x :: lis -> 
      if el.ab < x.ab then el :: x :: lis else if el.ab > x.ab then x :: insert_result  el lis else {ab=x.ab;ord=((x.ord+.el.ord)/.2.0)} ::lis;;

(***************************************************************************************)
(******************************************** MAIN ****************************)
(***************************************************************************************)
let main =
(*let ltask= parse_fich_task in*)
let nomfichier="/home/ROCQ/aoste/fndoye/simulations/tasks/nbtasks_varie/" in
let fic_result_success="/home/ROCQ/aoste/fndoye/simulations/result/multi_pro/duree/proc_fixed/duree_exact_algo_with_32_procs.ml" in
let oc=open_out fic_result_success in
let preemption_cost=1 in
let costCom= 1 in
let numbsuccess= ref 0 in
let list_period_diff=ref [] in
let lres= ref [] in
let ltaskbis= ref[] in
for nbproc=3 to 3 do
for k=3 to 3 do
 let duree_heuristique= ref 0.0 in
 let nomf=(nomfichier)^"SysTasks"^(string_of_int k)^"/" in 
 numbsuccess:=0 ;
 (*let nbproc=4 in*)
 let moy_load=ref 0.0 in
 let numT=ref 0 in
 list_period_diff:=[];
 (* Printf.printf "Iteration k=%d \n"k;*)
 for j=1 to 1 do 
  let fic=nomf^"setOfTask"^(string_of_int j)^".ml" in
  let r_parse=(parse_fic_tasks fic preemption_cost) in
  let ltask=r_parse.litasks in (* parse_fic_tasks fic preemption_cost *)
  ltaskbis:=ltask;
  moy_load:=(!moy_load)+.(r_parse.load);
  let indice=ref ((List.length ltask)-1) in
  let  input= ref 0 in
  let  output= ref 0 in

 while (!indice>=0)do
 let tache=(List.nth ltask
 !indice) in
   if(tache.lsucc=[]) then
    output:=(!output)+1;
   if(tache.lpred=[]) then
    input:=(!input)+1;
   if((find_task_list_period_diff tache !list_period_diff).trouve=false) then 
       list_period_diff:=(!list_period_diff)@[tache];
   indice:=(!indice)-1;
 done;
 let startTime= Unix.time() in
 let interval= compute_interval ltask in
 let li=schedulability_interval ltask interval.f_interval in
 let sched=(algo_exact  ltask nbproc interval li costCom preemption_cost !input !output) in
 if(sched.ischedulable=true) then 
   begin
   (*for i=0 to (Array.length lresult.lr)-1 do 
    let pr= lresult.lr.(i) in
    Printf.printf " ++++++ Processeur%d  +++++++\n" (pr.proc).idproc;
    for j=0 to (List.length pr.ltask)-1 do
     let ta = List.nth pr.ltask j in
     Printf.printf "t%d indice=%d idpro=%d\n" ta.id ta.indice ta.idpro;
    done;
    Printf.printf "\n";
   done;*)
    numbsuccess:=(!numbsuccess)+1;
   let endtTime= Unix.time() in 
   duree_heuristique :=(endtTime-.startTime);
   (* Printf.printf "Durée d'execution de oplusbis =%f\n" (endtTime-.startTime);*)
    Printf.printf "Le système est ordonnançable latence=%d\n"sched.latence_tasks ;
   end
  else
  Printf.printf "Système non ordonnançable j=%d \n"j;

  numT:=j;
 done;

(*lres:=(insert_result {ab=((!moy_load/.(float_of_int !numT)) );ord=((float_of_int !numbsuccess)/.(float_of_int !numT))} !lres);*)
   if(!numbsuccess!=0) then 
 lres:=(insert_result {ab=(float_of_int (List.length !ltaskbis) );ord=(!duree_heuristique)} !lres);
 (* Printf.fprintf oc "%f %f\n" (!moy_load/.(float_of_int !numT)) ((float_of_int !numbsuccess)/.(float_of_int !numT));*)
done;
done;

if(!numbsuccess!=0) then 
for i=0 to ((List.length !lres)-1) do
Printf.fprintf oc "%d  %f\n" (int_of_float (List.nth !lres i).ab) (List.nth !lres i).ord;
done;

close_out oc;


;;




