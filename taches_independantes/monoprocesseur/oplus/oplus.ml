
(* Définition des types*)
type otask =
{istart_time :  int ;
 itrans : int;
 perm  :int;
 schedule : int array ;
 schedulable: bool;
 loadT :float;
 wrt : int
(* makespan : int;*)
}

type task =
{id : int ;
 mutable firstActivation :int;
 wcet : int;
 period: int;
 deadline: int;
 preemption_cost: int ;
 wrtTask : int ;
}

type processeur=
{idproc : int;
 mutable t : task list ;
 mutable rotask  : otask;
 mutable load: float ;
}

type resultHeuristic =
{lprocesseurs : processeur list ;
  sched : bool;
  loadTasks : float;
  setWRT : int 
}

type result_parse=
{ litasks:task list;
  load:float;
}

let setFrtWrt t frt wrt =
{id=t.id;firstActivation=t.firstActivation;wcet=t.wcet;period=t.period;deadline=t.deadline;preemption_cost=t.preemption_cost;wrtTask=t.wrtTask};;

let compute_start_time ot t =
min ot.istart_time t.firstActivation;;
(****************************************************************************************)
let compute_trans_part ot t=
let trans= ref  t.firstActivation in 
while !trans < ot.itrans do 
   trans:=(!trans) + t.period
  done;
(!trans);;


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
(****************************************************************************************)
let compute_perm_part  ot t =
(*Printf.printf "permanente  %d" (lcm ot.perm t.period);*)
lcm ot.perm t.period;;
(****************************************************************************************)
let build_otask t =
let sched=Array.create (t.firstActivation+t.period) 0 in
let i = ref t.firstActivation in 
while !i<(t.firstActivation+t.wcet) do
 sched.(!i)<-t.id;
  i:=!i+1
 done;
(*
let k=ref 0  in
while !k<(Array.length sched)  do
  Printf.printf "%d "sched.(!k) ;
  k:=!k+1
 done; 
 Printf.printf "\n";*)

{istart_time=t.firstActivation;itrans=t.firstActivation;perm=t.period;schedule=sched;schedulable=true;loadT=(float_of_int t.wcet)/.(float_of_int t.period);wrt=t.wrtTask};;

let oplus ot t=
let start_time=compute_start_time ot t in
let trans=compute_trans_part ot t in
let perm=compute_perm_part ot t in
 
(*
Printf.printf "start time %d \n" start_time;
Printf.printf "trans ot1 %d \n"  trans;
Printf.printf "perm  %d \n" perm; *)
let sched= Array.create (trans+perm) 0 in
(*Printf.printf "size tab %d\n" (trans+perm);
Printf.printf "tab %d\n" (Array.length sched);*)
(*if(t.id=6) then *)
(*Printf.printf "id=%d Interval_Gossens = [%d, %d] trans=%d  perm=%d\n" t.id start_time (trans+perm) trans  perm;*) 


let frt=ref 0 in
let wrt=ref t.wcet in
let i=ref ot.istart_time in 
let schedulable =ref true in
let k= ref 0  in
let j=ref start_time in
let nbPreemption=ref  0 in
(*let rien= ref false ;*)
while (!k<(((Array.length sched)-t.firstActivation)/t.period)) & (!schedulable=true) do
  let exec = ref false in 
  let wcet=ref t.wcet in
  let responseTime= ref 0 in
  let release=ref (t.firstActivation+(!k*t.period)) in (* calcul des release time de la nouvelle tâche*)
  (*Printf.printf "release %d \n" !release ; *)
  
  while (!j<ot.istart_time)&(!j>=t.firstActivation) & !j<(!release+t.period)do 
     if !wcet > 0 then
      begin
         wcet:=!wcet-1; 
         sched.(!j)<-t.id;
         if(!k=0) then
         frt:=!frt+1;
         exec:= true;
         responseTime:= !responseTime+1;       
      end
     else
      begin
      exec:= false;
      end;
     (*Printf.printf "jP %d %d  wcet %d  \n" !j sched.(!j)  !wcet ; *)
     j:=!j+1; 
    done;

while (!j<(!release+t.period) )do (* Pour chaque periode de l'operande de droite*)
(*Printf.printf "i %d %d \n" !i ot.schedule.(!i) ; *)
 if(ot.schedule.(!i)!=0) then
     begin 
       sched.(!j)<-ot.schedule.(!i);
       if (!wcet > 0) then
         begin 
           responseTime:= !responseTime+1; 
           if(!exec = true) then 
              begin
                wcet:=!wcet+t.preemption_cost; 
                if (!j>trans) then 
                   nbPreemption:=(!nbPreemption)+1;
             end
           else
            exec:=(!exec);
             (*Printf.printf "coût de preemption  %d  %d \n" t.id t.preemption_cost;*)
             
               exec:=false ;
          end
     end
   else
      if (!wcet > 0) then
        begin
          if(!j>=t.firstActivation) then 
            begin
              if(!j>t.firstActivation) then 
             responseTime:= !responseTime+1; 
   
             wcet:=!wcet-1;  
             sched.(!j)<-t.id;
             exec:= true;
            end
        end
     else
       exec:= false;
       
   (*Printf.printf "j %d %d wcet  %d  i %d %d \n" !j sched.(!j) !wcet  !i ot.schedule.(!i) ; *)
   
   (* Printf.printf "j %d %d  wcet %d  \n" !j sched.(!j)  !wcet ;*)
     
   j:=!j+1;
   if(!i=(ot.itrans+ot.perm)-1) then 
     i:=ot.itrans 
   else
     i:=!i+1; 
  done;
(* Printf.printf "response Time  de la t%d sur son instance %d :  %d \n" t.id !k !responseTime ;*)
(* pour gerer le cas deadline!=period monotonic responseTime<=t.deadline *)
  if(!responseTime>t.deadline) then  
       schedulable:= false;
   if(!schedulable=true) then
    begin
     if(!k=0) then
      frt:=!responseTime;
     if(!responseTime >=(!wrt)) then 
       wrt:=!responseTime;
    end 
   else
   wrt:=t.period+1;
  k:=!k+1;
done;
let nb=perm/t.period in
let load =((float_of_int (nb*t.wcet+(!nbPreemption)))/.(float_of_int nb))/.( float_of_int t.period) in
(*Printf.printf "arret %d\n" (!j);*)
{istart_time=start_time;itrans=trans;perm=perm;schedule=sched;schedulable=(!schedulable);loadT=load;wrt=(!wrt)};;

(**********************************************************************)

let oplus_schedulability_condition ltask=
(*let schedulable= ref true in*)
let roplus=ref (build_otask (List.nth ltask 0)) in
let i=ref 1 in
while ((!i)<(List.length ltask))&((!roplus).schedulable=true) do
  let ta = List.nth ltask !i in 
  roplus:= (oplus (!roplus) ta) ;
  (*Printf.printf "tache=%d taille sched=%d \n" ta.id (Array.length (!roplus).schedule) ;*)
   i:=(!i)+1
done;

if((!roplus).schedulable=true) then 
begin

Printf.printf "Le système est ordonnançable \n";

(*
for j=0 to ((Array.length (!roplus).schedule)-1) do
Printf.printf "(%d, %d)" j (!roplus).schedule.(j);
done;*)
Printf.printf "\n"; 
end
else
Printf.printf "Le système est non ordonnançable !!!\n";
(!roplus).schedulable;;
(***************************)
let rec insert_task elem = function
  | [] -> [elem]
  | x :: l -> 
      if elem.period < x.period then elem :: x :: l else if elem.period > x.period then x :: insert_task  elem l else x ::elem:: l;;

(********************** Parser fich ****************************)
let parse_fic_tasks nomfic preemption_cost =
let ltask=ref[] in
let load=ref 0.0 in
let i=ref 1 in
let op = open_in (nomfic) in
let line =  ref (input_line op) in
 line :=(input_line op) ;
try
 line := input_line op;
let tache =  ref (Str.split  (Str.regexp " ") !line) in
while (!line != "")&((List.nth !tache 0).[0]!='i') do
 (*Printf.printf "%st \n" (List.nth tache 0);*)
  ltask:=insert_task  {id=(!i);firstActivation=(int_of_string (List.nth !tache 1));wcet=(int_of_string (List.nth !tache 2));period=(int_of_string (List.nth !tache 3));deadline=(int_of_string (List.nth !tache 4));preemption_cost=preemption_cost;wrtTask=(int_of_string (List.nth !tache 4))} (!ltask);
load:=(!load)+.((float_of_string (List.nth !tache 2))/.(float_of_string (List.nth !tache 3)));
 i:=(!i)+1;
 line := input_line op;
 tache:=(Str.split  (Str.regexp " ") !line);
done;
 {litasks=(!ltask);load=(!load)};
with End_of_file -> close_in op ;
 {litasks=(!ltask);load=(!load)};;



(*let parse_fic_tasks nomfic preemption_cost =
let ltask=ref[] in
let i=ref 1 in
let op = open_in (nomfic) in
let line =  ref (input_line op) in
 line := input_line op;
 line := input_line op;
let tache =ref (Str.split  (Str.regexp " ") !line) in
try
while (!line != "")&((List.nth !tache 0).[0]!='i')   do

 (*Printf.printf "%st \n" (List.nth tache 0);*)
  ltask:=insert_task  {id=(!i);firstActivation=(int_of_string (List.nth !tache 1));wcet=(int_of_string (List.nth !tache 2));period=(int_of_string (List.nth !tache 3));deadline=(int_of_string (List.nth !tache 4));preemption_cost=preemption_cost;wrtTask=(int_of_string (List.nth !tache 4))} (!ltask);

i:=(!i)+1;
 line := input_line op;
 tache:=(Str.split  (Str.regexp " ") !line);
done;
 !ltask;
 (*(!ltask_bis);*)
with End_of_file -> close_in op ;
 !ltask;;*)




(****************      ***************)
let main=
(*
let t_1={id=1;firstActivation=2;wcet=1;period=150;deadline=150;preemption_cost=0;wrtTask=50} in 
let t_2={id=2;firstActivation=0;wcet=2;period=275;deadline=275;preemption_cost=0;wrtTask=128} in
let t_3={id=3;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;wrtTask=131} in
let t_4={id=4;firstActivation=2;wcet=1;period=250;deadline=250;preemption_cost=0;wrtTask=50} in 
let t_5={id=5;firstActivation=0;wcet=2;period=200;deadline=200;preemption_cost=0;wrtTask=128} in
(*let t_6={id=6;firstActivation=2;wcet=2;period=130;deadline=130;preemption_cost=1;wrtTask=131} in*)*)
(*
let ltask=[t_2;t_1;t_3;t_4;t_5] in*)

let nomfichier="/home/ROCQ/aoste/fndoye/Desktop/simulations/tasks1/donnees_sauv/" in
let fic_result_success="/home/ROCQ/aoste/fndoye/simulations/result/success/oplus_without_preemption_cost.ml" in
let oc=open_out fic_result_success in
let preemption_cost=0 in
let numbsuccess= ref 0 in
for k=1 to 17 do 
 let numT=ref 0 in
 let moy_load=ref 0.0 in
let nomf=(nomfichier)^"SysTasks"^(string_of_int k)^"/" in 
 numbsuccess:=0 ;
for j=1 to 12 do
let fic=nomf^"setOfTask"^(string_of_int j)^".ml" in
let r_parse=(parse_fic_tasks fic preemption_cost) in
let startTime= Unix.time() in
let schedulable=oplus_schedulability_condition r_parse.litasks in
let endtTime= Unix.time() in 
Printf.printf "Durée d'execution de oplus =%fs\n" (endtTime-.startTime);
if(schedulable=true)then
 numbsuccess:=(!numbsuccess)+1;
 numT:=j;
  moy_load:=(!moy_load)+.(r_parse.load);
done;
Printf.fprintf oc "%f  %f\n" (!moy_load/.(float_of_int !numT)) ((float_of_int !numbsuccess)/.(float_of_int !numT));

Printf.printf "Taux de succès =%d/%d \n" !numbsuccess !numT;
done;
close_out oc;
;;
