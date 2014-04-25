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

(*
type taskSelected =
{mutable id: int;
 mutable ci: int;
}*)
type processeur=
{idproc : int;
 (*mutable t : task list ;*)
(*mutable schedule  : int array;*)
 mutable phi_t : int array;
 mutable schedulable : bool;
 mutable list_t : int list;
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
let rec sort = function
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
let compute_ci_t  ti t  p pre=
let ut=((t-ti.firstActivation) mod ti.period) in (* je garde pour ti que les valeurs de c_i sur l'instance considérée *)
 (* Printf.printf " ++++ t=%d t_p=%d  t_s=%d c%d(t-1)= %d \n" t pre.t_p pre.t_s ti.id ti.ci_t;*)
(* let ci= ref ti.ci_t in*)
if (ut=0) then 
 ti.wcet
 (*Printf.printf "ut=0 cit %d %d" ut ti.di_t.(ut)*)
else
if(p.phi_t.(pre.t_p)!=ti.id) then 
 ti.ci_t
else
if((p.phi_t.(t)=ti.id) || (p.phi_t.(t)!=ti.id) & ((pre.t_p+ti.ci_t)<=t)) then 
 max 0 ((pre.t_p+ti.ci_t)-t)
else
 (((pre.t_p+ti.ci_t)-t)+ti.preemption_cost);;
 
(*Printf.printf "\n";*)


(***************************************************************************************)
let compute_di_t ti t pre =
let ut=((t-ti.firstActivation) mod ti.period) in (* je garde pour ti que les valeurs de d_i sur l'instance considérée *)
if (ut=0) then 
 ti.deadline
else
if(ti.di_t >0) then 
max 0 ((pre.t_p+ti.di_t)-t)
else
0;;
(*Printf.printf "t=%d task%d d%d(t)=%d  \n" t ti.id ti.id ti.di_t.(ut);*)


(***************************************************************************************)
let phi_t  p t ltask pre =
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
    if (((pre.t_p +ta.ci_t)>t & (p.phi_t.(pre.t_p)=ta.id))||((ta.ci_t>0 & (p.phi_t.(pre.t_p)!=ta.id)))) then
        find:= true;
       i:=!i+1;
      
   end
  else
 i:=!i+1;
if ((!find)=true) then 
p.phi_t.(t)<-ta.id;
done;

p.phi_t;;


(**************************************************************************************||((cit.(ut)=0)&(dit.(ut)=0))   ||((0<cit.(ut))&(cit.(ut)=dit.(ut))&(p.phi_t(t)=(ta.id))) *)
let scheduling_test_t ltask p t pre =
let li=ref p.list_t in
let l=ref [] in
let i= ref 0 in
let schedulable= ref true in
while ((!i < ((List.length ltask))) & (!schedulable=true)) do
 let ta= ref (List.nth  ltask !i) in
(*let pre=pred_succ t (!l) in*)
(*Printf.printf "Avant test t=%d c%d=%d d%d=%d phi(t)=%d\n" t ta.id  ta.ci_t ta.id  ta.di_t p.phi_t.(t) ;*)
 if(t>=(!ta).firstActivation) then 
   begin

 (*Printf.printf "af %d %d et %d \n"t ta.firstActivation (t-ta.firstActivation);*)
  let cit=compute_ci_t !ta t p pre  in
 (*Printf.printf "****** t=%d c%d(t)=%d phi(t)=%d t_p=%d  t_s=%d \n" t (!ta).id cit p.phi_t.(t) pre.t_p pre.t_s;*)
  let dit= compute_di_t !ta t pre in  
 (* let ut=((t-ta.firstActivation) mod ta.period) in *)  
  if ((cit<dit)||((cit=0)&(dit=0))||((0<cit)&(cit=dit)&(p.phi_t.(t)=(!ta).id)) ) then 
    begin
    ta:= {id=(!ta).id;firstActivation=(!ta).firstActivation;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=cit;di_t=dit} ;
    l:=(!l)@ [!ta];
     (* Printf.printf "SSSS t=%d c%d=%d d%d=%d phi(t)=%d \n" t ti.id  cit ti.id  dit p.phi_t.(t);*)
     if((!ta).id=p.phi_t.(t)) then 
        begin
      (*  Printf.printf "Test";*)
         if ((t+(!ta).ci_t)<pre.t_s) then
           begin
          (* Printf.printf "t=%d est ajouté  \n" (t+(!ta).ci_t);*)
              li:= insert (t+(!ta).ci_t) !li

            end 
        end
   end 
  else
   schedulable:=false;
  end 
else
 l:=(!l) @  [{id=(!ta).id;firstActivation=(!ta).firstActivation;wcet=(!ta).wcet;period=(!ta).period;deadline=(!ta).deadline;preemption_cost=(!ta).preemption_cost;priority=(!ta).priority;ci_t=(!ta).ci_t;di_t=(!ta).di_t}];
i:=!i+1;


(*Printf.printf "t=%d phi(t)=%d task%d c%d(t)=%d  d%d=%d \n" t p.phi_t.(t) ta.id ti.id ti.ci_t ti.id ti.di_t*)
done;

{proc={idproc=p.idproc;phi_t=p.phi_t;schedulable=(!schedulable);list_t=(!li)};ltask=(!l)};;

(***************************************************************************************)
(********************************* Schedulability Condition ****************************)
(***************************************************************************************)
let new_schedulability_condition ltask interval li=
let ph=ref (Array.create (interval.f_interval) 0) in
let p=ref {idproc=1;phi_t=(!ph);schedulable=true;list_t=li} in
let t=ref 0 in

if(interval.r_min=0) then 
  t:= 0
else
 t:=(interval.r_min-1);
(*let j=(!t) in*)
let r= ref {proc=(!p);ltask=ltask} in
Printf.printf " interval [%d %d]\n"interval.r_min interval.f_interval;
while(((!t) < (interval.f_interval)) & ((!r).proc.schedulable=true)) do 
let pre= ref (pred_succ !t (!r).proc.list_t) in
 ph:=(phi_t (!r).proc !t (!r).ltask !pre);
 p:={idproc=(!p).idproc;phi_t=(!ph);schedulable=(!r).proc.schedulable;list_t=(!r).proc.list_t};
 r := (scheduling_test_t (!r).ltask !p !t (!pre));
(*
          Printf.printf "affichage de li_boucle\n";
          for i=0 to (List.length (!r).proc.list_t)-1 do
          Printf.printf "li:" ;
           Printf.printf " %d " (List.nth (!r).proc.list_t i) ;
          done;
         Printf.printf "\n";

Printf.printf "\n";*)

pre:= (pred_succ !t (!r).proc.list_t);
t:=((!pre).t_s);
done; 




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

(*let main =

let t_1={id=1;firstActivation=2;wcet=1;period=6;deadline=6;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in 
let t_2={id=2;firstActivation=0;wcet=50;period=100;deadline=100;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in
let t_3={id=3;firstActivation=2;wcet=2;period=12;deadline=12;priority=(1.0 /. (float_of_int 4));preemption_cost=1;ci_t= 0;di_t=0} in
let t_4={id=4;firstActivation=2;wcet=1;period=250;deadline=250;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in 
let t_5={id=5;firstActivation=0;wcet=2;period=128;deadline=128;priority=(1.0 /. (float_of_int 4));preemption_cost=0;ci_t= 0;di_t=0} in
let t_6={id=6;firstActivation=2;wcet=2;period=130;deadline=130;priority=(1.0 /. (float_of_int 4));preemption_cost=1;ci_t= 0;di_t=0} in*)

let t_1={id=1;firstActivation=2;wcet=1;period=150;deadline=150;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= 0;di_t=0} in
let t_2={id=2;firstActivation=0;wcet=2;period=275;deadline=275;preemption_cost=0;priority=(1.0 /. (float_of_int 4));ci_t= 0;di_t=0} in
let t_3={id=3;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;priority=(1.0 /. (float_of_int 12));ci_t=0;di_t=0} in
(*let t_4={id=4;firstActivation=2;wcet=1;period=250;deadline=250;preemption_cost=0;priority=(1.0 /. (float_of_int 6));ci_t= 0;di_t=0} in
let t_5={id=5;firstActivation=0;wcet=2;period=128;deadline=128;preemption_cost=0;priority=(1.0 /. (float_of_int 4));ci_t= 0;di_t=0} in
let t_6={id=6;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;priority=(1.0 /. (float_of_int 12));ci_t= 0;di_t=0} in


let ltask=[t_2;t_1;t_3;t_4;t_5;t_6;t_7;t_8;t_9;t_10;t_11;t_12] in*)


let ltask=[t_2;t_1;t_3] in (*t_4;t_5;t_6] in
let interval= compute_interval ltask in
let li=schedulability_interval ltask interval.f_interval in

(*
for i=0 to (List.length li)-1 do
Printf.printf "%d " (List.nth li i) ;
done;
Printf.printf "\n";*)




let startTime= Unix.time() in
new_schedulability_condition ltask interval li;
let endtTime= Unix.time() in 
Printf.printf "Durée d'execution de oplusbis =%fs\n" (endtTime-.startTime);
 ;;




