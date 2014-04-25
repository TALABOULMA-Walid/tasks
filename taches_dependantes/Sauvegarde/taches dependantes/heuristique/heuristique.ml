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
 mutable ci_t: int array;
 mutable di_t: int array;
 (*wrtTask : int ;*)
}

type processeur=
{idproc : int;
 (*mutable t : task list ;*)
(*mutable schedule  : int array;*)
 mutable phi_t : int array;
 mutable schedulable : bool;
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


(***************************************************************************************)
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
{r_min=(!r_min);f_interval=((!r_max)+2*(!h))} ;;

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
if (ut=0) then 
 ti.ci_t.(ut)<-ti.wcet
 (*Printf.printf "ut=0 cit %d %d" ut ti.di_t.(ut)*)
else
if(p.phi_t.(t-1)!=ti.id) then 
 ti.ci_t.(ut) <- ti.ci_t.(ut-1)
else
if((p.phi_t.(t)=ti.id) || (p.phi_t.(t)!=ti.id) & (ti.ci_t.(ut-1)=1)) then 
  ti.ci_t.(ut) <- (ti.ci_t.(ut-1)-1)
else
  ti.ci_t.(ut) <-((ti.ci_t.(ut-1)-1)+ti.preemption_cost);
   (*Printf.printf " Task%d est préempté à t=%d \n" ti.id t;*)
(*Printf.printf "t=%d phi(t)=%d task%d ut=%d c%d(t)=%d  \n" t p.phi_t.(t) ti.id  ut ti.id ti.ci_t.(ut);*)
(*Printf.printf "\n";*)
ti.ci_t;;

(***************************************************************************************)
let compute_di_t ti t=
let ut=((t-ti.firstActivation) mod ti.period) in (* je garde pour ti que les valeurs de d_i sur l'instance considérée *)
if (ut=0) then 
   ti.di_t.(ut)<-ti.deadline
else
if(ti.di_t.(ut-1)>0) then 
 ti.di_t.(ut)<-ti.di_t.(ut-1)-1
else
ti.di_t.(ut)<- 0;
(*Printf.printf "t=%d task%d d%d(t)=%d  \n" t ti.id ti.id ti.di_t.(ut);*)
ti.di_t;;

(***************************************************************************************)
let phi_t  p t ltask =
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
    if ((ta.ci_t.(ut-1)>1 & (p.phi_t.(t-1)=ta.id))||((ta.ci_t.(ut-1)>0 & (p.phi_t.(t-1)!=ta.id)))) then
      (* p.phi_t.(t)<-ta.id;*)
      find:= true;
     i:=!i+1
   end
  else
 i:=!i+1;
if ((!find)=true) then 
p.phi_t.(t)<-ta.id;
done;

p.phi_t;;


(**************************************************************************************||((cit.(ut)=0)&(dit.(ut)=0))   ||((0<cit.(ut))&(cit.(ut)=dit.(ut))&(p.phi_t(t)=(ta.id))) *)
let scheduling_test_t ltask p t =
let l=ref [] in
let i= ref 0 in
let schedulable= ref true in
while ((!i < ((List.length ltask))) & (!schedulable=true)) do

 let ta= List.nth  ltask !i in
 if(t>=ta.firstActivation) then 
   begin

 (*Printf.printf "af %d %d et %d \n"t ta.firstActivation (t-ta.firstActivation);*)
  let cit=compute_ci_t ta t p in
  let dit= compute_di_t ta t in  
  let ut=((t-ta.firstActivation) mod ta.period) in   

  if ((cit.(ut)<dit.(ut))||((cit.(ut)=0)&(dit.(ut)=0))||((0<cit.(ut))&(cit.(ut)=dit.(ut))&(p.phi_t.(t)=ta.id)) ) then 
    l:=(!l)@[{id=ta.id;firstActivation=ta.firstActivation;wcet=ta.wcet;period=ta.period;deadline=ta.deadline;preemption_cost=ta.preemption_cost;priority=ta.priority;ci_t=cit;di_t=dit}]
  else
(*Printf.printf "t=%d cit.(ut)=%d et dit.(ut)=%d\n" t cit.(ut) dit.(ut);*)
   schedulable:=false;
  end 
else
(*Printf.printf "t %d et ta.firstactivation %d" t ta.firstActivation;*)
 l:=(!l) @  [{id=ta.id;firstActivation=ta.firstActivation;wcet=ta.wcet;period=ta.period;deadline=ta.deadline;preemption_cost=ta.preemption_cost;priority=ta.priority;ci_t=ta.ci_t;di_t=ta.di_t}];
i:=!i+1
done;

{proc={idproc=p.idproc;phi_t=p.phi_t;schedulable=(!schedulable)};ltask=(!l)};;

(***************************************************************************************)
(********************************* Schedulability Condition ****************************)
(***************************************************************************************)
let schedulability_condition ltask =
let interval= compute_interval ltask in
let ph=ref (Array.create (interval.f_interval) 0) in
let p=ref {idproc=1;phi_t=(!ph);schedulable=true} in
let t=ref 0 in
if(interval.r_min=0) then 
  t:= 0
else
 t:=(interval.r_min-1);
(*let j=(!t) in*)
let r= ref {proc=(!p);ltask=ltask} in
Printf.printf " interval [%d %d]\n"interval.r_min interval.f_interval;
while(((!t) <interval.f_interval) & ((!r).proc.schedulable=true)) do 
 ph:=(phi_t !p !t ltask);
 p:={idproc=(!p).idproc;phi_t=(!ph);schedulable=(!p).schedulable};
 r := (scheduling_test_t (!r).ltask !p !t);

(*Printf.printf "\n";*)
t:=(!t)+1
done; 
(*Printf.printf "\n";*)

if (((!r).proc).schedulable=true) then 
begin
Printf.printf "Le système est ordonnançable \n";
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

let t_1={id=1;firstActivation=2;wcet=1;period=50;deadline=50;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= (Array.create (50) 0);di_t=(Array.create (50) 0)} in
let t_2={id=2;firstActivation=0;wcet=2;period=128;deadline=128;preemption_cost=0;priority=(1.0 /. (float_of_int 4));ci_t= (Array.create (128) 0);di_t=(Array.create (128) 0)} in
let t_3={id=3;firstActivation=2;wcet=2;period=131;deadline=131;preemption_cost=0;priority=(1.0 /. (float_of_int 12));ci_t= (Array.create (131) 0);di_t=(Array.create (131) 0)} in

let ltask=[t_2;t_1;t_3] in

schedulability_condition ltask ;;




