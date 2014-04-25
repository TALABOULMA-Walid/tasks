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
 (*mutable ci_t: int array;
 mutable di_t: int array;*)
 (*wrtTask : int ;*)
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
 (* mutable load: float ;*)
}

type interval=
{r_min: int ;
f_interval: int;
}

type result=
{ proc : processeur;
  ltask : task list ; 
}

type pred_succ_t=
{ t_p:int;
  t_s:int;
}

(* type resultHeuristic =
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
let rec insert elem = function
  | [] -> [elem]
  | x :: l -> 
      if elem < x then elem :: x :: l else if elem > x then x :: insert elem l else x :: l;;

(***************************)
let rec sort= function
  | [] -> []
  | x :: l -> insert x (sort l);;

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

(***************************************)
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
;;
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
let setTab tb t va =
let tab=Array.create (Array.length tb) 0 in
for i=0 to (Array.length tb) do
if(i=t) then 
tab.(i)<-va 
else
tab.(i)<-tb.(i)
done;
tab;;

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


(***************************************************************************************)
let phi_t  p t ltask =
 let pro= ref {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=p.idSelectedTask_t;idSelectedTask_t_1=p.idSelectedTask_t_1;list_t=p.list_t;t=p.t;t_1=p.t_1;next_t=p.next_t} in
let i= ref 0 in
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
    (* Printf.printf "Test p.t_1=%d ta.ci_t=%d dif=%d t=%d \n" p.t_1 ta.ci_t ((p.t_1+ta.ci_t)-t) t;*)
    if ((((p.t_1+ta.ci_t)>t)))||(ta.ci_t>0 & (p.idSelectedTask_t!=ta.id)) then (* idSelectedTask_t est equivalent au idSelectedTask_t-1 a ce niveau*)
        find:= true;
       i:=!i+1;
   end
  else
 i:=!i+1;
if ((!find)=true) then 
begin 
 p.phi_t.(t)<-ta.id;
 let t_1=p.idSelectedTask_t in
 let time1=p.t in
 pro:={idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=ta.id;idSelectedTask_t_1=t_1;list_t=p.list_t;t=t;t_1=time1;next_t=p.next_t};
end 
done;
if ((!find)=true) then 
 !pro
else
begin
 let t_1=p.idSelectedTask_t in
 let time2=p.t in
 {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=0;idSelectedTask_t_1=t_1;list_t=p.list_t;t=t;t_1=time2;next_t=p.next_t};
end;;

(***********)
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
{id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=0;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice} 
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
   {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=    (ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=0;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice} 
  else
  if (idSelectedTask_t_1=ta.id)&((t_1+ta.ci_t<=t)) then
   begin
    (*Printf.printf "Test t=%d id=%d b_%d=%d\n" t ta.id ta.id (ta.bi_t+1);*)
    {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=(ta.bi_t+1);lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice};
   end 
  else
     {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=(ta.bi_t);lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice}
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
    {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=    (ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=0;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice} 
  else
  begin
  if (idSelectedTask_t_1=ta.id)&((t_1+ta.ci_t<=t)) then
    {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=(ta.bi_t+1);lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice}
  else
     {id=(ta).id;firstActivation=(ta).firstActivation;wcet=(ta).wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;priority=(ta).priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=ta.bi_t;lpred=ta.lpred;lsucc=ta.lsucc;indice=ta.indice}  
 end
end
;;

(**************************************************************************************||((cit.(ut)=0)&(dit.(ut)=0))   ||((0<cit.(ut))&(cit.(ut)=dit.(ut))&(p.phi_t(t)=(ta.id))) *)
let scheduling_test_t ltask p t next_t=
let li=ref p.list_t in
let l=ref [] in
let i= ref 0 in
let next= ref next_t in
let schedulable= ref true in
 (*Printf.printf "length=%d \n" (List.length ltask);*)
while ((!i < ((List.length ltask))) & (!schedulable=true)) do
 let ta=ref (List.nth  ltask !i) in
let bi=ref (bi_t ltask !ta p.t_1 p.idSelectedTask_t_1 t).bi_t in
 if(t>=(!ta).firstActivation) then 
   begin
 (*Printf.printf "af %d %d et %d \n"t ta.firstActivation (t-ta.firstActivation);*)
  let cit=compute_ci_t !ta t p in
  let dit= compute_di_t !ta t p in  
 Printf.printf "t=%d c%d(t)=%d d%d=%d phi(t)=%d t_1=%d next_t=%d idSelectedTask=%d c%d=%d\n" t (!ta).id cit (!ta).id dit p.idSelectedTask_t p.t_1 next_t p.idSelectedTask_t (!ta).id cit;
   if ((!ta).id=p.idSelectedTask_t) &((t+cit)<next_t) then 
       next:=(t+cit);
(*((cit<dit) ) ||((cit=0)&(dit=0))||((0<cit)&(cit=dit)&(p.idSelectedTask_t=(!ta).id))  
((p.idSelectedTask_t=(!ta).id)&(cit<=dit))||((p.idSelectedTask_t!=(!ta).id)&((cit<=dit))&((t+cit)<=next))
(((0<cit)&(cit<=dit)&(p.idSelectedTask_t!=(!ta).id) &(((!next-(!ta).firstActivation) mod !ta.period)!=0))) ||((cit=0)&(dit=0))||((0<cit)&(cit<=dit)&(p.idSelectedTask_t=(!ta).id))
*)
  if ((cit<=dit)&((p.idSelectedTask_t=(!ta).id)||(cit=0)||(((!next-(!ta).firstActivation) mod !ta.period)!=0))) then 
    begin
 ta:= {id=(!ta).id;firstActivation=(!ta).firstActivation;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=cit;di_t=dit;bi_t=(!bi);lpred=(!ta).lpred;lsucc=(!ta).lsucc;indice=(!ta).indice} ;
    l:=(!l)@ [!ta];
    (* else
      if((!ta).id=p.idSelectedTask_t_1) then 
        bi:= (bi_t p !ta t).bi_t;*)
     end 
  else
   schedulable:=false;
 end 
else
 l:=(!l) @[{id=(!ta).id;firstActivation=(!ta).firstActivation;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=(!ta).ci_t;di_t=(!ta).di_t;bi_t=(!bi);lpred=(!ta).lpred;lsucc=(!ta).lsucc;indice=(!ta).indice}];

i:=!i+1;
(*Printf.printf "t=%d phi(t)=%d task%d c%d(t)=%d  d%d=%d \n" t p.phi_t.(t) ta.id ti.id ti.ci_t ti.id ti.di_t*)
done;

{proc={idproc=p.idproc;phi_t=p.phi_t;schedulable=(!schedulable);idSelectedTask_t=p.idSelectedTask_t;idSelectedTask_t_1=p.idSelectedTask_t_1;list_t=(!li);t=p.t;t_1=p.t_1;next_t=(!next)};ltask=(!l)};;


(*********************************)
let set_of_ready_tasks_t p ltask t=
let k=ref 0 in
let readyTasks= ref [] in
while (!k<(List.length ltask)) do 
let ta=(List.nth ltask !k) in 
 (*Printf.printf "++t=%d b%d=%d c%d=%d \n" t ta.id (bi_t ta p.t p.idSelectedTask_t t).bi_t ta.id (ta.ci_t) ;*)
let b_i= (bi_t ltask ta p.t p.idSelectedTask_t t).bi_t in
Printf.printf "******** bi_%d=%d c%d=%d t_1=%d id_t_1=%d \n" ta.id b_i ta.id ta.ci_t p.t p.idSelectedTask_t;

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
  Printf.printf "Succ Task%d k_%d%d=%d k_%d%d=%d diff=%d b_pred=%b\n" ta.id tj.id ta.id k_ij ta.id tj.id  k_ji bj !b_succ;
  i:=(!i)+1;
 done;

 if(!b_succ=true) then 
 begin
  let b_pred= ref true in
  i:=0;
  while (!i<(List.length ta.lpred)) & (!b_pred=true) do
   let ti=(List.nth ltask  (List.nth ta.lpred !i).indice )in
   let k_ij= k_i_j ti.period ta.period   in
   let k_ji= k_i_j ta.period  ti.period  in
   let bk=((bi_t ltask ta p.t p.idSelectedTask_t t).bi_t) in
   (*Printf.printf "Verif bi%d=%d \n"ti.id (bi_t ltask ti p.t p.idSelectedTask_t t).bi_t; +(bk/k_ji)  *)
   let bi=(((bi_t ltask ti p.t p.idSelectedTask_t t).bi_t)*k_ji)-((bk)*k_ij) in (*/k_ji*)
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
let p=ref {idproc=1;phi_t=(!ph);schedulable=true;idSelectedTask_t=0;idSelectedTask_t_1=0;list_t=li;t=0;t_1=0;next_t=0} in
let t=ref (List.nth li 0) in
(*if(interval.r_min=0) then 
  t:= 0
else
 t:= List.nth li 0);
let j=(!t) in*)
let r= ref {proc=(!p);ltask=ltask} in
let n= ref !t in

Printf.printf " interval [%d %d]\n"interval.r_min interval.f_interval;
let k=ref 0 in 

while(((!t) <(interval.f_interval) & ((!r).proc.schedulable=true)) )do 
Printf.printf "******************** A t=%d ***********************\n" !t ;
let readyTasks=(set_of_ready_tasks_t !p (!r).ltask !t) in
  if((!n)=(!t)) then 
  n:=next_t ((!r).proc.list_t) !k;
 (*let start= Unix.time() in*)
 p:=(phi_t (!r).proc !t readyTasks);
  Printf.printf "t=%d next=%d  \n" !t !n;
 (*p:={idproc=(!p).idproc;phi_t=(!ph);schedulable=(!p).schedulable};*)
  r := (scheduling_test_t (!r).ltask (!p) !t) !n;

(*
for i=0 to (List.length readyTasks) -1 do
let ta = List.nth readyTasks i in
Printf.printf "ready tasks id=%d b%d_t=%d \n" ta.id ta.id ta.bi_t;
done;*)


(*let endt= Unix.time() in 

if((endt-.start) != 0.0) then 
Printf.printf "t=%d, la durée d'execution de scheduling_test_t =%fs\n" !t (endt-.start);*)
if(!n=((!r).proc).next_t) then 
k:=(!k)+1;
t:=((!r).proc).next_t ;
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

;;


(***************************************************************************************)
(******************************************** MAIN ****************************)
(***************************************************************************************)


let main =
(*
let t_1={id=1;firstActivation=2;wcet=1;period=150;deadline=150;preemption_cost=0;wrtTask=50} in 
let t_2={id=2;firstActivation=0;wcet=2;period=180;deadline=180;preemption_cost=0;wrtTask=128} in
let t_3={id=3;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;wrtTask=131} in
let t_4={id=4;firstActivation=2;wcet=1;period=250;deadline=250;preemption_cost=0;wrtTask=50} in 
let t_5={id=5;firstActivation=0;wcet=2;period=128;deadline=128;preemption_cost=0;wrtTask=128} in
let t_6={id=6;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;wrtTask=131} in
let t_7={id=7;firstActivation=2;wcet=1;period=50;deadline=50;preemption_cost=0;wrtTask=50} in 
let t_8={id=8;firstActivation=0;wcet=2;period=128;deadline=128;preemption_cost=0;wrtTask=128} in
let t_9={id=9;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;wrtTask=131} in
let t_10={id=10;firstActivation=2;wcet=1;period=50;deadline=50;preemption_cost=0;wrtTask=50} in 
let t_11={id=11;firstActivation=0;wcet=2;period=128;deadline=128;preemption_cost=0;wrtTask=128} in
let t_12={id=12;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;wrtTask=131} in


let t_1={id=1;firstActivation=2;wcet=1;period=6;deadline=6;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in 
let t_2={id=2;firstActivation=0;wcet=2;period=4;deadline=4;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in
let t_3={id=3;firstActivation=2;wcet=2;period=6;deadline=6;priority=(1.0 /. (float_of_int 4));preemption_cost=1;ci_t= 0;di_t=0} in
let t_4={id=4;firstActivation=2;wcet=1;period=250;deadline=250;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in 
let t_5={id=5;firstActivation=0;wcet=2;period=128;deadline=128;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in
let t_6={id=6;firstActivation=2;wcet=2;period=130;deadline=130;priority=(1.0 /. (float_of_int 4));preemption_cost=1;ci_t= 0;di_t=0} in
let t_7={id=7;firstActivation=2;wcet=1;period=50;deadline=50;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in 
let t_8={id=8;firstActivation=0;wcet=2;period=128;deadline=128;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in
let t_9={id=9;firstActivation=2;wcet=2;period=130;deadline=130;priority=(1.0 /. (float_of_int 4));preemption_cost=1;ci_t= 0;di_t=0} in
let t_10={id=10;firstActivation=2;wcet=1;period=50;deadline=50;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in 
let t_11={id=11;firstActivation=0;wcet=2;period=128;deadline=128;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in
let t_12={id=12;firstActivation=2;wcet=2;period=130;deadline=130;priority=(1.0 /. (float_of_int 4));preemption_cost=1;ci_t= 0;di_t=0} in
let t_13={id=13;firstActivation=2;wcet=1;period=1872000;deadline=1872000;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in 
let t_14={id=14;firstActivation=2;wcet=1;period=250;deadline=250;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in 
let t_15={id=15;firstActivation=0;wcet=2;period=128;deadline=128;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in
let t_16={id=16;firstActivation=2;wcet=2;period=130;deadline=130;priority=(1.0 /. (float_of_int 4));preemption_cost=1;ci_t= 0;di_t=0} in
let t_17={id=17;firstActivation=2;wcet=1;period=50;deadline=50;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in 
let t_18={id=18;firstActivation=0;wcet=2;period=128;deadline=128;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0 }in
let t_19={id=19;firstActivation=2;wcet=2;period=130;deadline=130;priority=(1.0 /. (float_of_int 4));preemption_cost=1;ci_t= 0;di_t=0} in
let t_20={id=20;firstActivation=2;wcet=1;period=50;deadline=50;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in 
let t_21={id=11;firstActivation=0;wcet=2;period=128;deadline=128;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in
let t_22={id=22;firstActivation=2;wcet=2;period=130;deadline=130;priority=(1.0 /. (float_of_int 4));preemption_cost=1;ci_t= 0;di_t=0} in
let ltask=[t_2;t_1;t_3;t_4;t_5;t_6;t_7;t_8;t_9;t_10;t_11;t_12;t_13;t_14;t_15;t_16;t_17;t_18;t_19;t_20;t_21;t_22] in*)

let t_1=ref {id=1;firstActivation=3;wcet=1;period=6;deadline=6;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=1} in
let t_2=ref {id=2;firstActivation=2;wcet=1;period=24;deadline=24;preemption_cost=0;priority=(1.0 /. (float_of_int 4));ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=0} in
let t_3=ref {id=3;firstActivation=2;wcet=1;period=12;deadline=12;preemption_cost=0;priority=(1.0 /. (float_of_int 12));ci_t=0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=2} in
let t_4=ref {id=4;firstActivation=2;wcet=2;period=24;deadline=24;preemption_cost=0;priority=(1.0 /. (float_of_int 12));ci_t=0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=3} in
let t_5=ref {id=5;firstActivation=0;wcet=1;period=6;deadline=6;preemption_cost=0;priority=(1.0 /. (float_of_int 12));ci_t=0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=4} in

t_1:={id=1;firstActivation=0;wcet=1;period=6;deadline=6;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[!t_3];indice=1};
t_2:={id=2;firstActivation=1;wcet=1;period=24;deadline=24;preemption_cost=0;priority=(1.0 /. (float_of_int 4));ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[!t_3;!t_5];indice=0} ;
t_3:={id=3;firstActivation=3;wcet=1;period=12;deadline=12;preemption_cost=0;priority=(1.0 /. (float_of_int 12));ci_t=0;di_t=0;bi_t=0;lpred=[!t_1;!t_2];lsucc=[!t_4;!t_5];indice=2} ;
t_4:={id=4;firstActivation=0;wcet=1;period=24;deadline=24;preemption_cost=0;priority=(1.0 /. (float_of_int 4));ci_t= 0;di_t=0;bi_t=0;lpred=[!t_3];lsucc=[];indice=3} ;
t_5:={id=5;firstActivation=6;wcet=1;period=6;deadline=6;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= 0;di_t=0;bi_t=0;lpred=[!t_2;!t_3];lsucc=[];indice=4};
(*;
let ltask=[t_2;t_1;t_3] in ;t_4;t_5;t_6 ] in
let ltask=[t_2;t_1;t_3;t_4;t_5;t_6;t_7;t_8;t_9;t_10;t_11;t_12] in*)

let ltask=[!t_2;!t_1;!t_3;!t_4;!t_5] in(*;t_4;t_5;t_6;t_7;t_8] in*)
let interval= compute_interval ltask in
let li=schedulability_interval ltask interval.f_interval in

for i=0 to (List.length li)-1 do
Printf.printf "%d " (List.nth li i) ;
done;
Printf.printf "\n";

let startTime= Unix.time() in
new_schedulability_condition ltask interval li;
let endtTime= Unix.time() in 
Printf.printf "Durée d'execution de oplusbis =%fs\n" (endtTime-.startTime);
 ;;




