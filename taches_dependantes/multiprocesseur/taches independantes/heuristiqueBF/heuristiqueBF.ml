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


(****************************************************************************************)
(******************* oplus *********************)
(*let oplus ot t=
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
   if(!schedulable==true) then
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
{istart_time=start_time;itrans=trans;perm=perm;schedule=sched;schedulable=(!schedulable);loadT=load};;*)
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
(*********)
type setTasks =
{ltasks : task list;
loadSetTasks : float;
}

(* Tri de la liste des tâches *)
let rec triTask =function
  | [] -> []
  | x :: l -> insert x (triTask l)
and insert elem = function
  | [] -> [elem]
  | x :: l -> 
      if elem.period < x.period then elem :: x :: l else x :: insert elem l;;
(**************************************)
(*parser les fichiers de jeux de tâches  
let parse_fic nomfic=
 let ltasks = ref  [] in 
 let ic = open_in nomfic in
 let i=ref 0 in
 let line =  ref (input_line ic) in
 line := input_line ic;
try 
while (true) do
 line := input_line ic;
 let tache =  Str.split  (Str.regexp " ") !line in
  ltasks:={id=(!i);firstActivation=(int_of_string (List.nth tache 0));wcet=(int_of_string (List.nth tache 1));period= (int_of_string (List.nth tache 2));deadline=(int_of_string (List.nth tache 3));preemption_cost=1} :: !ltasks ;
i:=(!i)+1;
done
with 
| End_of_file -> close_in ic;
close_in ic;;*)

(*!ltasks;;*)
(*{ltasks=(!ltasks);loadSetTasks=0.0} ;;*)

(**************************************)
(* Heuristique d'ordonnancement multiprocesseur*)
let computeLoad  load ta=
load+.((float_of_int ta.wcet)/.(float_of_int ta.period));;
(**************************************)
let setListproc lp p=
let newlp= ref [] in
for i=0 to (List.length lp)-1 do
 if ((List.nth lp i).idproc != p.idproc) then 
    newlp:=(List.nth lp i)::(!newlp)
else
    newlp:=p::(!newlp)
done;
(!newlp) ;;


(**************************************)
(************** Heuristic BF ***********)
(*t : la liste des tâches et p: le tableau des processeurs *)
let heuristicBF t m =
let wrt= ref min_int in
let  p = ref [] in
let nbProc= ref 1 in
(*allocation des m premières tâches les plus prioritaires aux m premiers processeurs  *)
let oc =open_out "/home/ROCQ/aosteroc/fndoye/ExactAlgoritmNew/heuristique/debugHeuristiqueBF.ml"  in
let load = ref 0.0 in 
for i=0 to 0 do
  let ti=List.nth t i in
  Printf.fprintf oc "tâche %d %d \n" i ti.period;
  p:={idproc=(i+1);t=[ti];rotask=build_otask ti;load=(float_of_int ti.wcet)/.(float_of_int ti.period)}::!p;
  load := (!load)+. ((float_of_int ti.wcet)/.(float_of_int ti.period));
done;
  (*Printf.printf "proc %d\n" (List.length !p);*)
let schedulable = ref true in
let i =ref 1 in
while (!i< (List.length t) & ((!schedulable)=true)) do 
     let ta = List.nth t !i in 
     Printf.fprintf oc "tâche %d %d \n" !i ta.period;
     let minLoad = ref max_float in
     let b_indice = ref 0 in
     load:= (!load) +. ((float_of_int ta.wcet)/.(float_of_int ta.period));
     let b_ot= ref {istart_time=0;itrans=0;perm=0;schedule=Array.create (1) 0 ;schedulable=false;loadT=0.0;wrt=0} in

     for j= 0 to  !nbProc-1  do
       let ot= oplus (List.nth !p j).rotask ta in
       if (ot.schedulable=true) then 
       begin
         let load =(List.nth !p j).load +. ot.loadT in 
         if ((1.0-.load)<= (!minLoad)) then  
           begin
            minLoad:= load;
            b_indice:=j;
            b_ot:=ot;
           end 
       end
     done; 
    
     if ((!minLoad) != max_float) then 
       begin 
         if(!wrt<=(ta.firstActivation+(!b_ot).wrt))then 
           wrt:=(ta.firstActivation+(!b_ot).wrt);
       let tai={id=(ta). id;firstActivation=(ta).firstActivation;wcet=(ta). wcet;period=(ta).period;deadline=(ta).deadline;preemption_cost=(ta).preemption_cost;wrtTask=(!wrt)} in
        let ps={idproc=(List.nth !p (!b_indice)).idproc;t=tai::(List.nth !p (!b_indice)).t;rotask=(!b_ot);load=(List.nth !p (!b_indice)).load+.((float_of_int ta.wcet)/.(float_of_int ta.period))} in
        p:= (setListproc !p ps);
        (*(List.nth !p (!b_indice)).t=ta::(List.nth !p (!b_indice)).t;
        (List.nth !p (!b_indice)).rotask=(!b_ot); 
        (List.nth !p (!b_indice)).load=(!minLoad); *)
        schedulable := true;
       end 
     else
         if((!nbProc)<m) then 
           begin
              let pro={idproc=((!nbProc)+1);t=[ta];rotask=build_otask ta;load=(float_of_int ta.wcet)/.(float_of_int ta.period)} in 
               p:=(!p)@ [pro];
               nbProc:=(!nbProc+1) ;
           end
          else
            schedulable := false; 
     i:=!i+1;
done;
close_out oc;
{lprocesseurs=(!p);sched=(!schedulable);loadTasks=(!load);setWRT=(!wrt)};;

(*********************************************************************)
let print_result r=
for i =0 to (List.length r.lprocesseurs) -1 do 
   let p=List.rev r.lprocesseurs in
   Printf.printf "Proc%d:" (List.nth p i).idproc;
   for j=0 to  (List.length (List.nth p i).t)-1 do
    Printf.printf " t%d:" (List.nth (List.nth p i).t j).id;
  done; 
 Printf.printf "\n";
done;;

let print_tasks lt=
for i = 0 to (List.length lt) -1 do 
 Printf.printf "tache%d %d %d %d %d\n" (List.nth lt i).id (List.nth lt i).firstActivation (List.nth lt i).wcet (List.nth lt i).period (List.nth lt i).deadline  ;
done;;
(*********************************************************************)
(*Périodes multiples *)
let multiple perm p=
((perm mod p)=0)|| ((p mod perm)=0);;
(*********************************************************************)
let periodDifferent l element=
let i=ref 0 in
let differentElement= ref true in
while(!i<(List.length l) & (!differentElement=true)) do
 if(((element.firstActivation=(List.nth l !i).firstActivation)&(element.period=(List.nth l !i).period))|| ((element.firstActivation=(List.nth l !i).firstActivation)&((multiple element.period (List.nth l !i).period) =true))) then 
   differentElement:= false;
   i:=(!i)+1;
done;
if(!differentElement=true) then
(element::l)
else
l;;
(*********************************************************************)
(*Périodes multiples *)
let multiple perm p=
((perm mod p)=0)|| ((p mod perm)=0);;
(******************************************************************************************)
let moyenProc r=
let moy= ref 0.0 in
let n=(List.length r.lprocesseurs) in
for i=0 to n-1 do
   moy:= (!moy)+.(1.0-. (List.nth r.lprocesseurs i).load);
done;
!moy/.(float_of_int n );;
(******************************************************************************************)
(*Main *)
let main=
let nomficResult="/home/ROCQ/aosteroc/fndoye/ExactAlgoritmNew/results/resultHeuristiqueBFCPUTime.ml" in
let nomficResultBF="/home/ROCQ/aosteroc/fndoye/ExactAlgoritmNew/results/resultHeuristiqueBFLoad.ml" in
let nomficResultSucces="/home/ROCQ/aosteroc/fndoye/ExactAlgoritmNew/results/resultHeuristiqueBFSucessRatio.ml" in
let suc =open_out  nomficResultSucces in
let load =open_out  nomficResultBF in
let oc =open_out nomficResult in
let ldifferentPeriod= ref [] in
(*let setTask="/home/ROCQ/aosteroc/fndoye/ExactAlgoritmNew/setTasks/setTask" in*)
 (*Fournir le nombre de fichier de tâches à exécuter*)
(*Printf.printf "Test\n";*)
for l=1 to 1 do
let nbSuccess=ref 0 in
let moyLoad=ref 0.0 in
let nbDifferentPeriod =ref 0 in
let nbTask=ref 1 in
for k= 1 to 10 do 
(* Printf.printf "Taskset %d %d\n" l k;*)
let nomfic= ref "/home/ROCQ/aosteroc/fndoye/ExactAlgoritmNew/setTasks/setOfTask.ml" in
(*let nomfic= ref "/home/ROCQ/aosteroc/fndoye/ExactAlgoritmNew/setTasks/setOfTask.ml" in
let nomfic= ref "/home/ROCQ/aosteroc/fndoye/ExactAlgoritmNew/setTasks/harmonique/setOfTask.ml" in*)
let ltasks = ref  [] in 
nomfic:= (!nomfic) ^ (string_of_int k);
(*nomfic:=setTask^(string_of_int l)^"/setOfTask.ml"^(string_of_int k);*)
let ic = open_in (!nomfic) in
let i=ref 0 in
let loadSetTask = ref 0.0 in
(*let nbDifferentPeriod =ref 0 in*)
let line =  ref (input_line ic) in
try 
while(!line != "") do
 line := input_line ic;
 (*Printf.printf "%s \n" !line ;*)
 let tache =  Str.split  (Str.regexp " ") !line in
if((List.length tache)!= 0) then 
begin
  ltasks:={id=(!i+1);firstActivation=(int_of_string (List.nth tache 0));wcet=(int_of_string (List.nth tache 1));period= (int_of_string (List.nth tache 2));deadline=(int_of_string (List.nth tache 3));preemption_cost=1;wrtTask=(int_of_string (List.nth tache 1))} :: !ltasks ;
 ldifferentPeriod:=periodDifferent !ldifferentPeriod (List.nth !ltasks !i);
i:=(!i)+1;
loadSetTask:=(!loadSetTask) +. ((float_of_int (int_of_string (List.nth tache 1))) /.(float_of_int (int_of_string (List.nth tache 2))));
nbTask:= (!nbTask)+1 ;
 (*Printf.printf "Sys % d Set %d ligne %d \n" l k !i;*)
 (*Printf.printf "Taille %d \n" (List.length tache) ;
 ldifferentPeriod:=periodDifferent !ldifferentPeriod (int_of_string (List.nth tache 2));*)
end 
done
with 
| End_of_file -> close_in ic;
close_in ic;
ltasks:= triTask (!ltasks) ;
nbDifferentPeriod:= List.length (!ldifferentPeriod);
(*print_tasks !ltasks;*)
(* m est le nombre de processeurs*)
 moyLoad:=(!moyLoad)+. !loadSetTask;
for m=4+k to (4+k)  do
(*mesurer le temps de l'heuristique*)
let startTime= Unix.time() in
let r=heuristicBF !ltasks m in
let endtTime= Unix.time() in 
if (r.sched==true) then 
 begin 
  Printf.fprintf oc "%f %f %d %d\n" !loadSetTask (endtTime-.startTime) k (4+k);
  Printf.fprintf load "%f %f %d\n" !loadSetTask (moyenProc r) k;
  nbSuccess:=(!nbSuccess+1);
  Printf.printf "Success  %d  %d \n" l k;
(*(endtTime-.startTime)*)
   (* Printf.fprintf sucBF "%d %f\n" m (moyenProc r);*)
  (*  if(k=10) then
  Printf.fprintf sucBF "%d %f\n" m (moyenProc r) ;*)
 
(*  print_result r;
 Printf.printf "\n";*)
 end 
done; 
done;
 (*let moy=(!moyLoad) /. (7.0) in*)
 let successRatio= (float_of_int !nbSuccess) /. (6.0) in
 let nbMult=(!nbTask- (!nbDifferentPeriod)) in
 (*Printf.fprintf suc "%d %f %d\n"  !nbDifferentPeriod moy !nbSuccess ;*)
  Printf.fprintf suc "%f  %f\n" ((!moyLoad /. 6.0) /. (float_of_int nbMult)) successRatio;
done;
(*close_out oc;
close_out sucBF*)
close_out suc;
