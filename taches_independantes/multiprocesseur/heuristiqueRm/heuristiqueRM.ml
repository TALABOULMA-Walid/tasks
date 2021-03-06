(* Définition des types*)
type otask =
{istart_time :  int ;
 itrans : int;
 perm  :int;
 schedule : int array ;
 schedulable: bool;
(* makespan : int;*)
}
type task =
{id : int ;
 mutable firstActivation :int;
 wcet : int;
 period: int;
 deadline: int;
 preemption_cost: int ;
}

type processeur=
{idproc : int;
 mutable t : task list ;
 mutable load: float ;
}

type resultHeuristic =
{lprocesseurs : processeur list ;
  sched : bool;
  loadTasks : float
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

{istart_time=t.firstActivation;itrans=t.firstActivation;perm=t.period;schedule=sched;schedulable=true};;


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
(*Printf.printf "size tab %d\n" (trans+perm);
Printf.printf "tab %d\n" (Array.length sched);*)
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
       schedulable:= false;
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
(*Printf.printf "arret %d\n" (!j);*)
{istart_time=start_time;itrans=trans;perm=perm;schedule=sched;schedulable=(!schedulable)};;

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
(*Test d'ordonnançabilité RM *)
let schedulabityTestRM p ta=
let load=computeLoad  p.load ta in
let n=(List.length p.t) +1 in
(load<=(exp (1.0/.(float_of_int n))*.(log 2.0)));;

(**************************************)
(*t : la liste des tâches et p: le tableau des processeurs *)
let heuristicRM t m=
let  p = ref [] in
(*allocation des m premières tâches les plus prioritaires aux m premiers processeurs  *)
let oc =open_out "/home/falou/ExactAlgoritmNew/heuristiqueRm/debugHRM.ml"  in
let load = ref 0.0 in 
for i=0 to m-1 do
  let ti=List.nth t i in
  p:={idproc=(i+1);t=[ti];load=(float_of_int ti.wcet)/.(float_of_int ti.period)}::!p;
  load := (!load)+. ((float_of_int ti.wcet)/.(float_of_int ti.period));
done;
  (*Printf.printf "proc %d\n" (List.length !p);*)
let schedulable = ref true in
let i =ref m in
while (!i< (List.length t) & ((!schedulable)=true)) do 
     Printf.fprintf oc "tâche %d \n" !i;
     let minLoad = ref max_float in
     let b_indice = ref 0 in
     let ta = List.nth t !i in 
     load:= (!load) +. ((float_of_int ta.wcet)/.(float_of_int ta.period));
     for j= 0 to  (List.length !p)-1  do
       let rs=schedulabityTestRM (List.nth !p j) ta in
       if (rs=true) then 
       begin
         let load = computeLoad (List.nth !p j).load ta in 
         if (load<= (!minLoad)) then  
           begin
            minLoad:= load;
            b_indice:=j;
           end 
       end
     done; 

     if ((!minLoad) != max_float) then 
       begin 
        let ps={idproc=(List.nth !p (!b_indice)).idproc;t=ta::(List.nth !p (!b_indice)).t;load=(!minLoad)} in
        p:= (setListproc !p ps);
        (*(List.nth !p (!b_indice)).t=ta::(List.nth !p (!b_indice)).t;
        (List.nth !p (!b_indice)).rotask=(!b_ot); 
        (List.nth !p (!b_indice)).load=(!minLoad); *)
        schedulable := true;
       end 
     else
         schedulable := false; 
     i:=!i+1;
done;
close_out oc;
{lprocesseurs=(!p);sched=(!schedulable);loadTasks=(!load)};;

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
done

(******************************************************************************************)
(*Main *)
let main=
let nomficResult="/home/falou/ExactAlgoritmNew/results/resultHeuristqueRM.ml" in
let nomficResultSucces="/home/falou/ExactAlgoritmNew/results/resultHeuristqueSuccessHRM.ml" in
let oc =open_out nomficResult in
let suc =open_out  nomficResultSucces in
(* Fournir le nombre de fichier de tâches à exécuter*)
(*let setTask="/home/falou/ExactAlgoritmNew/setTasks/setTask" in*)
for l=1 to 10 do
let nbSuccess=ref 0 in
let moyLoad=ref 0.0 in
for k= 1 to 10 do 
 Printf.printf "Taskset %d\n" k;
let nomfic= ref "/home/falou/ExactAlgoritmNew/setTasks/setOfTask.ml" in
let ltasks = ref  [] in 
nomfic:= (!nomfic) ^ (string_of_int k);
(*nomfic:=setTask^(string_of_int l)^"/setOfTask.ml"^(string_of_int k);*)
 (*Printf.printf "%s \n" !nomfic ;*)
let ic = open_in (!nomfic) in
let i=ref 0 in
let line =  ref (input_line ic) in
try 
while(!line != "") do
 line := input_line ic;
 (*Printf.printf "%s \n" !line ;*)
 let tache =  Str.split  (Str.regexp " ") !line in
if((List.length tache)!= 0) then 
 (*Printf.printf "Taille %d \n" (List.length tache) ;*)
  ltasks:={id=(!i+1);firstActivation=(int_of_string (List.nth tache 0));wcet=(int_of_string (List.nth tache 1));period= (int_of_string (List.nth tache 2));deadline=(int_of_string (List.nth tache 3));preemption_cost=1} :: !ltasks ;
i:=(!i)+1;
done
with 
| End_of_file -> close_in ic;
close_in ic;
ltasks:= triTask (!ltasks) ;

(*print_tasks !ltasks;*)
(* m est le nombre de processeurs*)
let m=10  in
(*mesurer le temps de l'heuristique*)
let startTime= Unix.time() in
let r=heuristicRM !ltasks m in
let endtTime= Unix.time() in 
if (r.sched=true) then 
 begin 
  moyLoad:=(!moyLoad)+.r.loadTasks ;
  nbSuccess:=(!nbSuccess+1);
  Printf.fprintf oc "%d %f\n" k (endtTime-.startTime);
  (*print_result r;
  Printf.printf "\n";*)
 end 
done;
 let moy=(!moyLoad) /. (10.0) in
 let successRatio= (float_of_int !nbSuccess) /. (10.0) in
 Printf.fprintf suc "%d %f %f\n" l moy successRatio;
done;
close_out oc;
close_out suc
