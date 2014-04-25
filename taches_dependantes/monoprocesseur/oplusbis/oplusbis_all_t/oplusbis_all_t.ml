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
let compute_ci_t  ti t  p=
let ut=((t-ti.firstActivation) mod ti.period) in (* je garde pour ti que les valeurs de c_i sur l'instance considérée *)
(* let ci= ref ti.ci_t in*)

 (*Printf.printf "t=%d idSelectedTask(t)=%d idSelectedTask(t-1)=%d \n" t p.idSelectedTask_t p.idSelectedTask_t_1 ;*)
if (ut=0) then 
 ti.wcet
else
if(p.idSelectedTask_t_1!=ti.id) then 
 ti.ci_t
else
if((p.idSelectedTask_t=ti.id) || (p.idSelectedTask_t!=ti.id) & (ti.ci_t=1)) then 
  ti.ci_t-1
else
 (((ti.ci_t)-1)+ti.preemption_cost);;
   (*Printf.printf " Task%d est préempté à t=%d \n" ti.id t;*)
(*Printf.printf "\n";*)


(***************************************************************************************)
let compute_di_t ti t=
let ut=((t-ti.firstActivation) mod ti.period) in (* je garde pour ti que les valeurs de d_i sur l'instance considérée *)
if (ut=0) then 
 ti.deadline
else
if(ti.di_t >0) then 
ti.di_t-1
else
0;;
(*Printf.printf "t=%d task%d d%d(t)=%d  \n" t ti.id ti.id ti.di_t.(ut);*)


(***************************************************************************************)
let phi_t  p t ltask =
 let pro= ref {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=p.idSelectedTask_t;idSelectedTask_t_1=p.idSelectedTask_t_1} in
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
     (*Printf.printf "Test t=%d  id=%d c%d=%d \n" (t-1)  ta.id  ta.id ta.ci_t;*)
    if ((ta.ci_t>1 & (p.idSelectedTask_t=ta.id))||((ta.ci_t>0 & (p.idSelectedTask_t!=ta.id)))) then (* idSelectedTask_t est equivalent au idSelectedTask_t-1 a ce niveau*)
        find:= true;
       i:=!i+1;
    
   end
  else
 i:=!i+1;
if ((!find)=true) then 
begin 
 p.phi_t.(t)<-ta.id;
 let t_1=p.idSelectedTask_t in
 pro:={idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=ta.id;idSelectedTask_t_1=t_1};
end 
done;
if ((!find)=true) then 
 !pro
else
begin
 let t_1=p.idSelectedTask_t in
 {idproc=p.idproc;phi_t=p.phi_t;schedulable=p.schedulable;idSelectedTask_t=0;idSelectedTask_t_1=t_1};
end;;


(**************************************************************************************||((cit.(ut)=0)&(dit.(ut)=0))   ||((0<cit.(ut))&(cit.(ut)=dit.(ut))&(p.phi_t(t)=(ta.id))) *)
let scheduling_test_t ltask p t =
let l=ref [] in
let i= ref 0 in
let schedulable= ref true in
while ((!i < ((List.length ltask))) & (!schedulable=true)) do
 let ta= List.nth  ltask !i in
(*Printf.printf "Avant test t=%d c%d=%d d%d=%d phi(t)=%d\n" t ta.id  ta.ci_t ta.id  ta.di_t p.phi_t.(t) ;*)
 if(t>=ta.firstActivation) then 
   begin

 (*Printf.printf "af %d %d et %d \n"t ta.firstActivation (t-ta.firstActivation);*)
  let cit=compute_ci_t ta t p in
  let dit= compute_di_t ta t in  

 (* let ut=((t-ta.firstActivation) mod ta.period) in *)  
  if ((cit<dit)||((cit=0)&(dit=0))||((0<cit)&(cit=dit)&(p.idSelectedTask_t=ta.id)) ) then 
    begin
    let ti= {id=ta.id;firstActivation=ta.firstActivation;wcet=ta.wcet;period=ta.period;deadline=ta.deadline;preemption_cost=ta.preemption_cost;priority=ta.priority;ci_t=cit;di_t=dit} in
    l:=(!l)@ [ti];
     (* Printf.printf "SSSS t=%d c%d=%d d%d=%d phi(t)=%d\n" t ti.id  cit ti.id  dit p.phi_t.(t);*)
   end 
  else
   schedulable:=false;
  end 
else
 l:=(!l) @  [{id=ta.id;firstActivation=ta.firstActivation;wcet=ta.wcet;period=ta.period;deadline=ta.deadline;preemption_cost=ta.preemption_cost;priority=ta.priority;ci_t=ta.ci_t;di_t=ta.di_t}];
i:=!i+1;

(*Printf.printf "t=%d phi(t)=%d task%d c%d(t)=%d  d%d=%d \n" t p.phi_t.(t) ta.id ti.id ti.ci_t ti.id ti.di_t*)
done;
{proc={idproc=p.idproc;phi_t=p.phi_t;schedulable=(!schedulable);idSelectedTask_t=p.idSelectedTask_t;idSelectedTask_t_1=p.idSelectedTask_t_1};ltask=(!l)};;

(***************************************************************************************)
(********************************* Schedulability Condition ****************************)
(***************************************************************************************)
let new_schedulability_condition ltask interval =

let ph=ref (Array.create (interval.f_interval) 0) in
let p=ref {idproc=1;phi_t=(!ph);schedulable=true;idSelectedTask_t=0;idSelectedTask_t_1=0} in
let t=ref 0 in
if(interval.r_min=0) then 
  t:= 0
else
 t:=(interval.r_min-1);
(*let j=(!t) in*)
let r= ref {proc=(!p);ltask=ltask} in
Printf.printf " interval [%d %d]\n"interval.r_min interval.f_interval;
while(((!t) <interval.f_interval) & ((!r).proc.schedulable=true)) do 
 p:=(phi_t !p !t (!r).ltask);
 (*p:={idproc=(!p).idproc;phi_t=(!ph);schedulable=(!p).schedulable};*)
 r := (scheduling_test_t (!r).ltask (!p) !t);

(*Printf.printf "\n";*)
t:=(!t)+1
done; 
(*Printf.printf "\n";*)

if (((!r).proc).schedulable=true) then 
begin
Printf.printf "Le système est ordonnançable \n";
Printf.printf "Taille=%d " (Array.length ((!r).proc).phi_t);
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
let t_12={id=12;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;wrtTask=131} in*)



(*let ltask=[t_2;t_1;t_3;t_4;t_5;t_6;t_7;t_8;t_9;t_10;t_11;t_12;t_13;t_14;t_15;t_16;t_17;t_18;t_19;t_20;t_21;t_22] in*)

let t_1={id=1;firstActivation=2;wcet=1;period=150;deadline=150;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= 0;di_t=0} in
let t_2={id=2;firstActivation=0;wcet=2;period=275;deadline=275;preemption_cost=0;priority=(1.0 /. (float_of_int 4));ci_t= 0;di_t=0} in
let t_3={id=3;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;priority=(1.0 /. (float_of_int 12));ci_t=0;di_t=0} in
let t_4={id=4;firstActivation=2;wcet=1;period=250;deadline=250;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= 0;di_t=0} in
let t_5={id=5;firstActivation=0;wcet=2;period=200;deadline=200;preemption_cost=0;priority=(1.0 /. (float_of_int 4));ci_t= 0;di_t=0} in
let t_6={id=6;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;priority=(1.0 /. (float_of_int 12));ci_t=0;di_t=0} in
let t_7={id=7;firstActivation=2;wcet=1;period=250;deadline=250;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= 0;di_t=0} in
let t_8={id=8;firstActivation=0;wcet=2;period=200;deadline=200;preemption_cost=0;priority=(1.0 /. (float_of_int 4));ci_t= 0;di_t=0} in
(*
let t_1={id=1;firstActivation=2;wcet=1;period=150;deadline=150;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= 0;di_t=0} in
let t_2={id=2;firstActivation=0;wcet=2;period=275;deadline=275;preemption_cost=0;priority=(1.0 /. (float_of_int 4));ci_t= 0;di_t=0} in
let t_3={id=3;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;priority=(1.0 /. (float_of_int 12));ci_t=0;di_t=0} in
let t_6={id=6;firstActivation=2;wcet=2;period=131;deadline=131;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= 0;di_t=0} in*)
(*let t_6={id=6;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;priority=(1.0 /. (float_of_int 12));ci_t= 0;di_t=0} in
let ltask=[t_2;t_1;t_3;t_4;t_5;t_6 ] in
let ltask=[t_2;t_1;t_3;t_4;t_5;t_6;t_7;t_8;t_9;t_10;t_11;t_12] in*)

let ltask=[t_2;t_1;t_3;t_4;t_5;t_6;t_7;t_8] in
let interval= compute_interval ltask in
let startTime= Unix.time() in
new_schedulability_condition ltask interval;
let endtTime= Unix.time() in 
Printf.printf "Durée d'execution de oplusbis =%fs\n" (endtTime-.startTime);
 ;;




