(*open Printf;*)

type otask =
{istart_time :  int ;
 itrans : int;
 perm  :int;
 schedule : int array ;
 schedulable: bool;
(* makespan : int;*)
}

type rotask =
{roplus :otask ;
 wrt : int;
}

type task =
{id : int ;
 mutable firstActivation :int;
 wcet : int;
 period: int;
 deadline: int;
 preemption_cost: int ;
}

let setFrtWrt t frt wrt =
{id=t.id;firstActivation=t.firstActivation;wcet=t.wcet;period=t.period;deadline=t.deadline;preemption_cost=t.preemption_cost};;

let compute_start_time ot t =
min ot.istart_time t.firstActivation;;
(****************************************************************************************)
let compute_trans_part ot t=
let trans= ref  t.firstActivation in 
while !trans < ot.istart_time do 
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

{roplus={istart_time=t.firstActivation;itrans=t.firstActivation;perm=t.period;schedule=sched;schedulable=true};wrt=t.wcet};;


(****************************************************************************************)
let oplus ot t=
let start_time=compute_start_time ot t in
let trans=compute_trans_part ot t in
let perm=compute_perm_part ot t in
(*
Printf.printf "start time %d \n" start_time;
Printf.printf "trans ot1 %d \n"  trans;
Printf.printf "perm  %d \n" perm; *)
let sched= Array.create (trans+perm) 0 in
let frt=ref 0 in
let wrt=ref t.wcet in
let i=ref ot.istart_time in 
let schedulable =ref true in
let k= ref 0  in
let j=ref start_time in


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
                wcet:=!wcet+t.preemption_cost; 

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
    schedulable:= false ;
   if(!schedulable=true) then 
    begin
     if(!k=0) then
      frt:=!responseTime;
     if(!responseTime >=(!wrt)) then 
       wcet:=!responseTime;
    end 
   else
   wrt:=t.period+1;
  k:=!k+1;
done;
  (* t=setFrtWrt t !frt !wrt;
   t.wrt=(!wrt);*)

  (* let l =ref ((trans+perm)-1) in
   while (((!l)>=start_time) & (sched.(!l)=0)) do
     l:=(!l)-1;
   done;  *)
{roplus={istart_time=start_time;itrans=trans;perm=perm;schedule=sched;schedulable=(!schedulable)};wrt=(!wrt)};;



(****************************************************************************************)
let print_otask ot =
Printf.printf "intervalle [%d  %d]" ot.istart_time (ot.itrans+ot.perm);
Printf.printf "\n" ;
(*
for j=0 to (Array.length ot.schedule)-1 do 
 Printf.printf " %d " j ;
done;
Printf.printf "\n" ;*)

for i=0 to (Array.length ot.schedule)-1 do 
  if i=ot.itrans  then 
    Printf.printf "|" ;
    Printf.printf "%d" ot.schedule.(i)
done;
Printf.printf "\n" ;;
(****************************************************************************************)
let main =
(*let task1={id=1;firstActivation=0;wcet=3;period=15;deadline=7} in
let task2={id=2;firstActivation=5;wcet=2;period=6;deadline=6} in
let task3={id=3;firstActivation=3;wcet=4;period=10;deadline=10} in
let task5={id=5;firstActivation=15;wcet=5;period=60;deadline=47} in*)

let task1={id=1;firstActivation=9;wcet=1;period=6;deadline=6;preemption_cost=0;} in
let task2={id=2;firstActivation=13;wcet=3;period=12;deadline=9;preemption_cost=2} in
let task3={id=3;firstActivation=5;wcet=2;period=15;deadline=15;preemption_cost=2} in
(*let task4={id=4;firstActivation=0;wcet=3;period=24;deadline=21;preemption_cost=1} in

let task5={id=5;firstActivation=15;wcet=5;period=60;deadline=47;preemption_cost=1} in
let task1={id=1;firstActivation=1;wcet=3;period=10;deadline=10} in
let task2={id=2;firstActivation=0;wcet=2;period=10;deadline=10} in
let task3={id=3;firstActivation=3;wcet=1;period=6;deadline=6} in*)

let list_task=[task2;task3] in
(*print_otask (build_otask task1) ;*)

let r= ref (build_otask task1) in 
let i=ref 0 in 
let schedulable = ref true in 
 while (!schedulable=true) &( !i<(List.length list_task) )do
    r:= oplus !r.roplus (List.nth list_task !i);
    schedulable:=((!r).roplus).schedulable;
    i:=!i+1;
done ;
 (*print_otask r*) 
if (!schedulable=true) then
  begin  
   Printf.printf "System  Schedulable \n" ;
   print_otask (!r).roplus
end  
else
 Printf.printf "System not Schedulable \n"
