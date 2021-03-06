(*** BEGIN ***)
(*** SINGLE TASK DATA STRUCT ***)
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
 			mutable t_read_data:int
 			}
	and
		buffer_b=
			{idBuf:int;
 			priority_buf: float;
 			setTasks_may_use_b : task list;
			}
(*** END ***)

(*** BEGIN ***)
(*** GRAPH OF TASKS DATA STRUCT ***)
type graphe_task=
{ graph :  (task array) array;
  nbTasks : int;
  longueur: int;
  hauteur : int;
  nb_input : int;
  nb_output: int;
  possible : bool;
  list_tasks :task list
}
(*** END ***)

(*** BEGIN ***)
(*** TASK_FOUND DATA STRUCT ( RETURN OF SEARCHING IN A LIST OF TASK ) ***)
type task_found=
{ta : task;
firstAct: int;
trouve : bool;
idP : int
} 
(*** END ***)

(*** BEGIN ***)
(*** !!!!!!!!! UNUSED DATA STRUCT !!!!!!!! ***)
type l_h=
{l:int; h:int}
(*** END ***)


(*** BEGIN ***)
(*** FIND_TASK_LIST ROUTINE ***)
(*** val find_task_list : task -> task list -> task_found = <fun> ***)
let  find_task_list ta l = 
	let vbool=ref false in
	let i=ref 0 in
	let re=ref {ta={id=0;
						firstActivation=0;
						firstActivation_2=0;
						wcet=1;
						period=6;
						deadline=6;
						deadline_2=6;
						preemption_cost=0;
						priority=(1.0/. 6.0);
						ci_t= 0;
						di_t=0;
						bi_t=0;
						lpred=[];
						lsucc=[];
						indice=1;
						priority_t=(1.0/. 6.0);
						lbuffer=[];
						set_blocked_tasks=[];
						idpro=1;
						ltime_data_succ=[|{idTask=3;t_read_data=12}|]
						};
						
					firstAct=0;
					trouve=false;
					idP=0
					} in
					
	while (!i<List.length l) & (!vbool=false) do
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

(*** END ***)

(*** BEGIN ***)
(*** FIND_TASK_LIST_PRED ***)
(*** val find_task_list_pred : 'a -> 'a list -> bool = <fun> ***)
(*** !!!!! UNUSED !!!!! ***)
let  find_task_list_pred id l = 
let vbool=ref false in
let i=ref 0 in
(*let re=ref id in*)
while (!i<List.length l) &(!vbool=false) do
 let idt=(List.nth l !i) in 
 if(id=idt) then 
  begin
   vbool:=true;
   i:=(!i)+1;
  end
else
 i:=(!i)+1;
done; 
!vbool;;
(*** END ***)


(*** BEGIN ***)
(*** GEN_PRED ROUTINE: ***)
(*** val gen_pred :  int -> task array array -> 'a -> int -> int -> task list ref -> int ref -> task = <fun> ***)
let gen_pred num_task g h j ni_1 l nta=
	let nbpred= ref 0 in
	if (!nta!=1) & (ni_1!=0) then
 		nbpred :=((Random.int ni_1)+1)
	else
		if((List.length !l)=ni_1) then 
 			nbpred:=1
		else
			if(ni_1=1)then 
 				nbpred:=ni_1
	else
		if(!nta=1) then
nbpred:= (max (ni_1-(List.length !l)) (Random.int ni_1)+1);

let ltask=ref [] in
     let i=ref 0 in
  
    while !i<(!nbpred) do

     let len= (ni_1) in
     let pred= ref g.(j-1).((Random.int len)) in

     
     let re= ref (find_task_list !pred !ltask) in  
     let re2=ref (find_task_list !pred !l) in

     while ( (((!re.trouve)=true)||(!pred.id=0))&((!re2.trouve=true)&((List.length !l)!=ni_1)))  do
       
      let ind= (Random.int len) in 
      pred:=(g.(j-1).(ind));
       
      re:=(find_task_list !pred !ltask);
      re2:=(find_task_list !pred !l);
     done;
     let r=(find_task_list !pred !ltask ) in
      if (r.trouve=false) then 
       ltask:=(!ltask)@[!pred];

       l:=(!l)@[!pred];
       nta:=(!nta)+1;
       i:=(!i)+1;
    done; 


{id=num_task;firstActivation=0;firstActivation_2=0;wcet=1;period=6;deadline=6;deadline_2=6;preemption_cost=0;priority=(1.0/. 6.0);ci_t= 0;di_t=0;bi_t=0;lpred=(!ltask);lsucc=[];indice=(num_task-1);priority_t=(1.0/. 6.0);lbuffer=[];set_blocked_tasks=[];idpro=1;ltime_data_succ=[|{idTask=3;t_read_data=12}|]};;
(*** END ***)

(******************** Gen l et h ********************)
let gen_l_h n n_input n_output=
let l=ref (Random.int n) in
let h=ref (Random.int n) in
let max_tasks=ref (((!l*(!h))-(2*(!h)-n_input-n_output)))in
while (!max_tasks<n) ||(n<(!l+(!h-1)) ||(n_input >(!h))||(n_output>(!h))) do
l:=(Random.int n) ;
h:=(Random.int n) ;
max_tasks:=(((!l*(!h))-(2*(!h)-n_input-n_output)));
done;
{l=(!l);h=(!h)};
 ;;



(********************************************** Création d'un graphe de tâches ***************************************************)
let creation_de_graphe_tache n l h n_input n_output=
let ta={id=0;firstActivation=0;firstActivation_2=0;wcet=1;period=6;deadline=6;deadline_2=6;preemption_cost=0;priority=(1.0/. 6.0);ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=1;priority_t=(1.0/. 6.0);lbuffer=[];set_blocked_tasks=[];idpro=1;ltime_data_succ=[|{idTask=3;t_read_data=12}|]} in
let g= ref {graph=(Array.create l (Array.create h ta)) ;nbTasks=n;longueur=l; hauteur=h;nb_input=n_input;nb_output=n_output;possible=true;list_tasks=[]} in
let max_tasks=((l*h)-(2*h-n_input-n_output)) in
(*Printf.printf "max_task=%d \n"max_tasks;*)
if (max_tasks>=n) & (n>=(l+h-1) &(n_input <=h)&(n_output<=h)) then
 begin
  let gr= Array.create l (Array.create h ta) in
  let max_ta =ref  (n-(n_input+n_output)) in
 (* Printf.printf "max_ta=%d \n" !max_ta;*)
  let num_task= ref 1 in
  let n_j= ref n_input in 
  let ltask = ref [] in
  let preemption_cost=1 in
  (*** Input Task****************)
     (*Printf.printf "****************** Test init **************** \n";*)
 for j=0 to l-1 do
  let tab= ref  (Array.create h ta) in
  for i=0 to  h-1 do
   let ti={id=(!num_task);firstActivation=0;firstActivation_2=0;wcet=1;period=6;deadline=6;deadline_2=6;preemption_cost=preemption_cost;priority=(1.0/. 6.0);ci_t= 0;di_t=0;bi_t=0;lpred=[];lsucc=[];indice=(!num_task-1);priority_t=(1.0/. 6.0);lbuffer=[];set_blocked_tasks=[];idpro=0;ltime_data_succ=[|{idTask=3;t_read_data=12}|]} in
    if(i<(!n_j))&(j=0) then 
     begin
    (!tab).(i)<-(ti);
    num_task:=(!num_task)+1;
    ltask:=(!ltask)@[ti]
    end
  (* Printf.printf "%d%d=%d " 0 i gr.(0).(i).id ;*)

  done;
  gr.(j)<-(!tab) ;
 done;
 (******* Control Task****************)
  let nb_i_1=ref  n_input in
 
  if((n_input<h)&(n_output<h)) then 
   begin
      let l_i=(ref (Random.int l)) in
      while (!l_i=0)||(!l_i=l-1) do 
       l_i:=(Random.int l);
      done;
       let nj= (l-2) in
       let max_ta_b =(!max_ta) in
       let m= ref 0 in
       for j=1 to l-2 do  
       let lk=ref [] in
    
      (* if(j<(!l_i)) then
       begin 
       let nj=(l-1)-(j+1) in *)

         if(!l_i=j) then 
            n_j:=h 
         else
          if(j=(l-2))then
           begin
            n_j:=(!max_ta) ;
           (*((max_ta_b-h)/(nj-1))+1;*)
           (* m:=(!m)+1;*)
           end
         else
         if(((max_ta_b-h) mod (nj-1))!=(!m)) then
          begin
           n_j:=((max_ta_b-h)/(nj-1))+1;
           m:=(!m)+1;
          end
         else
         n_j:=((max_ta_b-h)/(nj-1));

  (* Printf.printf "****************** j=%d max_ta=%d  n_j=%d l_i=%d num_task=%d max_ta_b=%d ************************\n"j !max_ta  !n_j !l_i !num_task max_ta_b;*)
     
      let nta =ref !n_j in
    (* Printf.printf "\n";*)
     for i=0 to (!n_j-1) do
      (*Printf.printf "Test : j=%d i=0 tji=%d" j gr.(j).(0);*)
        
      let ti=(gen_pred !num_task gr h j !nb_i_1 lk nta) in
       
      gr.(j).(i)<-(ti);
      (*******************)
      for l=0 to (List.length ti.lpred)-1 do
       (*Printf.printf "+Test+\n" ;*)
       let ta=(List.nth ti.lpred l) in
        let ki= ref 0 in
         while (ta.id!=(gr.(j-1).(!ki).id))&(!ki<h) do
         ki:=(!ki)+1; 
         done;
         gr.(j-1).(!ki)<-{id=ta.id;firstActivation=ta.firstActivation;firstActivation_2=ta.firstActivation_2;wcet=ta.wcet;period=ta.period;deadline=ta.deadline;deadline_2=ta.deadline_2;preemption_cost=ta.preemption_cost;priority=ta.priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=ta.bi_t;lpred=ta.lpred;lsucc=ta.lsucc@[ti];indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro;ltime_data_succ=ta.ltime_data_succ};
      done;

      (*******************)
 num_task:=(!num_task)+1;
 ltask:=(!ltask)@[ti];  
     done;

      max_ta:=(!max_ta)-(!n_j);
     nb_i_1:=(!n_j)
    done; 
    
   end
 else
if ((n_input=h)||(n_output=h)) then 
   begin

       let nj= (l-2) in
       let max_ta_b =(!max_ta) in
       let m= ref 0 in
    for j=1 to l-2 do
     let lk=ref [] in


      if(j=(l-2)) then (*& ((max_ta_b mod nj)<(!m))*) 
         begin
          n_j:=(!max_ta);
        end
      else
      if((max_ta_b mod nj)!=(!m)) then 
        begin
         n_j:=(max_ta_b/nj)+1;
         m:=(!m)+1
        end
        else
        n_j:=(max_ta_b/nj);

     (*Printf.printf "++++++++++ j=%d max_ta=%d  n_j=%d +++++++++++++++\n"j !max_ta !n_j;*)
      let nta =ref !n_j in

      for i=0 to (!n_j-1) do
      let ti=(gen_pred !num_task gr h j !nb_i_1 lk nta) in
      gr.(j).(i)<-(ti);
      ltask:=(!ltask)@[ti];

      (*******************)
      for l=0 to (List.length ti.lpred)-1 do
      (* Printf.printf "+Test+\n" ;*)
       let ta=(List.nth ti.lpred l) in
        let ki= ref 0 in
         while (ta.id!=(gr.(j-1).(!ki).id))&(!ki<h) do
         ki:=(!ki)+1; 
         done;
         gr.(j-1).(!ki)<-{id=ta.id;firstActivation=ta.firstActivation;firstActivation_2=ta.firstActivation_2;wcet=ta.wcet;period=ta.period;deadline=ta.deadline;deadline_2=ta.deadline_2;preemption_cost=ta.preemption_cost;priority=ta.priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=ta.bi_t;lpred=ta.lpred;lsucc=ta.lsucc@[ti];indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro;ltime_data_succ=ta.ltime_data_succ};
      done;

      (*******************)
      num_task:=(!num_task)+1;
  
     done;
     max_ta:=(!max_ta)-(!n_j);
     nb_i_1:=(!n_j)
    done; 
   end
else
n_j:=n_output;

 (******* Output Task****************)
   n_j:=n_output;
   let lk=ref [] in
   let nta =ref !n_j in
  for i=0 to !n_j-1 do
   (*Printf.printf "Testtttt num=%d 228\n" !num_task ;*)
   let ti=(gen_pred !num_task gr h (l-1) !nb_i_1 lk nta ) in
  (* Printf.printf "Testtttt num=%d 3336\n" !num_task ;*)
    gr.(l-1).(i)<-(ti);
      (*******************)
      for k=0 to (List.length ti.lpred)-1 do
      (* Printf.printf "+Test+\n" ;*)
       let ta=(List.nth ti.lpred k) in
        let ki= ref 0 in
         while (ta.id!=(gr.(l-2).(!ki).id))&(!ki<h) do
         ki:=(!ki)+1; 
         done;
         gr.(l-2).(!ki)<-{id=ta.id;firstActivation=ta.firstActivation;firstActivation_2=ta.firstActivation_2;wcet=ta.wcet;period=ta.period;deadline=ta.deadline;deadline_2=ta.deadline_2;preemption_cost=ta.preemption_cost;priority=ta.priority;ci_t=ta.ci_t;di_t=ta.di_t;bi_t=ta.bi_t;lpred=ta.lpred;lsucc=ta.lsucc@[ti];indice=ta.indice;priority_t=ta.priority_t;lbuffer=ta.lbuffer;set_blocked_tasks=ta.set_blocked_tasks;idpro=ta.idpro;ltime_data_succ=ta.ltime_data_succ};
      done;
      (*******************)
   num_task:=(!num_task)+1;
   ltask:=(!ltask)@[ti];
  done;


(*
let list_def= ref [] in
for j=((l-1)  to 1 do
 for i=0 to (h-1) do 
  let ti=(List.nt !ltask i
 done
done;*)


g:={graph=gr;nbTasks=n;longueur=l; hauteur=h;nb_input=n_input;nb_output=n_output;possible=true;list_tasks=(!ltask)};
 end 
else 
g:={graph=(!g.graph);nbTasks=n;longueur=l; hauteur=h;nb_input=n_input;nb_output=n_output;possible=false;list_tasks=[]};

!g;;

 (*||((!sum_u-.(!next_sum))>((u/.(float_of_int n))))||((!next_sum/.(float_of_int (n-i)))<((u/.(float_of_int n))))
||((!next_sum/.(float_of_int (n-i)))<((u/.(float_of_int n))))     ((!next_sum/.(float_of_int (n-i)))<((u/.(float_of_int n))))

(((!next_sum)/.((float_of_int (n-i))))>1.0)|| (!next_sum=(!sum_u)) 
*)

(********************** UUnifast **************************)
(**********************************************************)
let u_unifast1 n u=
Random.self_init();
let vbool= ref false in
let tab=ref (Array.create n 0.0) in
let sum_u= ref u in
let next_sum= ref 0.0 in
let uk=ref u in
let tsum=ref 0.0 in
if((u /.(float_of_int n) )<=1.0) then
 begin

(*let k=ref 1 in*) 
  let i=ref 1 in
(*let arret=ref false in*)
while (!sum_u>0.0) do

  uk:=(!sum_u);
(*Printf.printf "tsum=%f u=%f vbool=%b sum_u=%f\n " !tsum u !vbool !sum_u;*)
  (*tsum:=0.0 ; *)
  (*k:=(!k)+1;*)
  i:=1;
  while (!i<=n)&(!uk>0.0)do
   next_sum :=((Random.float !sum_u));

   while ((!sum_u-.(!next_sum))>1.0)||(((!sum_u-.(!next_sum))>((u/.(float_of_int n)))))  do
    next_sum := ((Random.float !sum_u));
   
   done;

     !tab.(!i-1)<-((!tab).(!i-1)+.((!sum_u-.(!next_sum)))); (*/.3.0*) 

   tsum:=(!tsum)+.(!sum_u-.(!next_sum));
   sum_u:=(!next_sum);
   i:=(!i)+1;
 done;



sum_u:=(u-.(!tsum));

if(!tsum=u) then
vbool:=true;
done;
end 
else
tab:=(Array.create n 0.0);

Printf.printf "Verif tsum=%f sum_u=%f \n " !tsum !sum_u;
!tab;;

(****************** UUn **********)
let u_unifast n u=

u_unifast1 n u;;

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

(************************ Multiple x et y  *********************)
let multiple_x_y x y =
if((x mod y)=0)||((y mod x)=0) then
true
else
false;; 

(***************************Compute k_ij**********************)
let k_i_j period_i period_j =
let r= (period_j mod period_i) in 
let q=(period_j / period_i) in
if(r!=0) then 
q+1 
else
q;;
(**************** insert ***********************)
let rec insert elem = function
  | [] -> [elem]
  | x :: l -> 
      if elem < x then elem :: x :: l else if elem > x then x :: insert elem l else x :: l;;
(************* Génération de tâches (période, wcet, activation dat) ******************)

let gener_task lp t_u max_ppcm max_period n=
Random.self_init();
let ltask= ref [] in
let comp_ppcm= ref 1 in
 let lmultiple=ref [10] in (*[5;10;60;30;90] *)

for i=0 to (n-1) do
 let ti=(List.nth lp i) in
 if (ti.lpred=[]) then
  begin 
    let per= ref 10 in (*((Random.int 10)+2)*)

    while ((lcm !comp_ppcm !per)>max_ppcm)||((List.length !lmultiple)<(n*n))do
       Random.self_init();
      per:=((Random.int max_period)+4);
      (*per:=(!per/2);*)
      let bon_per= ref true in
      let nk= ref 0 in
      while (!bon_per=true) &(!nk<(List.length !lmultiple)) do
        if((multiple_x_y !per (List.nth !lmultiple !nk))=false) then (*||(!per=(List.nth !lmultiple !nk))*)
          bon_per:=false;
         nk:=(!nk)+1;
      done;
      (*bon_per:=true;*)
     if(!bon_per=true)then
        lmultiple:= (!lmultiple)@[!per]   (*(insert !per (!lmultiple) ) ;*)
    done;

    (*Printf.printf "Test avant len_multiple=%d\n" (List.length !lmultiple);*)

   per:=(List.nth !lmultiple (Random.int (List.length !lmultiple)));
   let wcet=ref (floor (t_u.(i)*.(float_of_int !per))) in

  while (!wcet=0.0) do
   per:=(List.nth !lmultiple (Random.int (List.length !lmultiple)));
   wcet:=(floor (t_u.(i)*.(float_of_int !per)));
  done;

   let r1=(Random.int !per) in (*(Random.int max_firstAct)*)
   ltask:=(!ltask)@[{id=ti.id;firstActivation=r1;firstActivation_2=r1;wcet=(int_of_float !wcet);period=(!per);deadline=(!per);deadline_2=(!per);preemption_cost=ti.preemption_cost;priority=(1.0/. (float_of_int !per));ci_t= 0;di_t=0;bi_t=0;lpred=ti.lpred;lsucc=ti.lsucc;indice=ti.indice;priority_t=(1.0/. (float_of_int !per));lbuffer=[];set_blocked_tasks=[];idpro=ti.idpro;ltime_data_succ=ti.ltime_data_succ}];  
  comp_ppcm:=(lcm !comp_ppcm !per) ;
  end 
  else 
  begin
   
    let maxr=ref min_int in
   
    let minr=ref max_int in 
    let mult=ref false in
     

    let per= ref (List.nth !lmultiple (Random.int (List.length !lmultiple))) in
    let wcet=ref (floor (t_u.(i)*.(float_of_int !per))) in
   
    while (!wcet=0.0) do
  
    Random.self_init();
    per:=(List.nth !lmultiple (Random.int (List.length !lmultiple)));
     wcet:=(floor (t_u.(i)*.(float_of_int !per)));
    done; 

      let k=ref 0 in  
    
      mult:=true ;  (*&(!mult=true)*)
     let c=ref 0 in
     while ((!k<(List.length ti.lpred)))do
      let pred= (List.nth !ltask (List.nth ti.lpred !k).indice) in
      let kij= (k_i_j pred.period  !per) in
       if(!maxr<(pred.firstActivation+((kij-1)*pred.period)+pred.wcet)) then 
          begin
           maxr:=(pred.firstActivation+((kij-1)*pred.period)+pred.wcet) ;
           c:=pred.wcet;
          end 
          else
          c:= (!c);
       if(!minr>(pred.firstActivation+((kij-1)*pred.period)+pred.wcet)) then 
           minr:=(pred.firstActivation+((kij-1)*pred.period)+pred.wcet);

       if((multiple_x_y !per pred.period)=false) then
        mult:=false;
       k:=(!k)+1;
     done;


   comp_ppcm:=(lcm !comp_ppcm !per) ;
 
   let r1=(!maxr+(!c)) in 


   
   ltask:=(!ltask)@[{id=ti.id;firstActivation=r1;firstActivation_2=r1;wcet=(int_of_float !wcet);period=(!per);deadline=(!per);deadline_2=(!per);preemption_cost=ti.preemption_cost;priority=(1.0/. (float_of_int !per));ci_t= 0;di_t=0;bi_t=0;lpred=ti.lpred;lsucc=ti.lsucc;indice=ti.indice;priority_t=(1.0/. (float_of_int !per));lbuffer=[];set_blocked_tasks=[];idpro=ti.idpro;ltime_data_succ=ti.ltime_data_succ}];    
  end
done;
!ltask;;



(*** BEGIN ***)
(*** MAIN ***)

let main =
	(*** default parameters values ***)
	let n = ref 8 in								           (*** nombre de taches ***)
	let l = ref 4 in           							  (*** longueur du graphe ***)
	let h = ref 3 in            							  (*** hauteur du graphe ***)
	let nset = ref 1 in										  (*** nombre de jeu de taches ==> nbre de fichiers générés ***) 
	let n_input= ref 3 in        							  (*** nombre d'entrée du graph ***)	
	let n_output= ref 2 in									  (*** nombre de sorties du graph ***)
	let u=ref 0.5 in											  (*** taux d'utilisation ***)
	let max_ppcm= ref 1000000 in							  (*** max ppcm des periodes des taches ***)	
	let max_period= ref 100 in								  (*** max period d'une tache ***)

	
	(*** arguments parsing utility ***)	
	let speclist = [	("-ntask", Arg.Set_int n, " : Sets the number of tasks to generate inside the graph");
							("-l", Arg.Set_int l, " : Sets the LENGTH of the graph \n 
																		!RMQ!: will affect the DEPENDENCY (succ-pred) bitween the tasks \n
																		!RMQ2!: may render the graph generation UNFEASABLE if \"uncorrectly set\"");
							("-h", Arg.Set_int h, " : Sets the HEIGHT of the graph \n 
																		!RMQ!: will affect the PARALLELISM of the tasks \n
																		!RMQ2!: may render the graph generation UNFEASABLE if \"uncorrectly set\"");
							("-nset", Arg.Set_int nset," : Sets the number of graphs to generate, each one will go inside a seperate file");
							("-input", Arg.Set_int n_input," : Sets the number of inputs of the graph");
							("-output", Arg.Set_int n_output," : Sets the number of outputs of the graph");
							("-u" , Arg.Set_float u , " : Sets the percentage of ressource usage 0.5 is the default and SAFE value");
							("-ppcm", Arg.Set_int max_ppcm, " : Sets the maximum tolerated PPCM of the tasks' periods (HYPERPERIOD)");
							("-T" , Arg.Set_int max_period, " : Sets the maximum period for each task "); 
						] in
	 let usage_msg = "\n\nTASKGEN is the routine that generates the graphs of tasks with the specified constraints \
	 						 on their periodes, deadlines, ppcm ... etc \n
*****************************************************************************************
Each set of tasks is stored in a file with a specific format \nthe default parameters are : \n
*************************\n
number of tasks  	==> 8 \n
graph length     	==> 4 \n
graph width	   	==> 3 \n
number of sets   	==> 1 \n
graph inputs     	==> 3 \n
graph outputs    	==> 2 \n
ratio use  U		==> 0.5 \n
max PPCM		==> 1000000 \n
max period	  	==> 100 \n" in
	 
	 Arg.parse speclist print_endline usage_msg;
	(*** paremeters display ***)
	print_endline ("NOW TRY GENERATING ............" );
	print_endline ( string_of_int !nset ^ " SETS ");
	print_endline ( string_of_int !n		^ " TASKS per SET ");	
	print_endline ("in a GRAPH H x L = " ^ string_of_int !h ^ " x " ^ string_of_int !l);
	print_endline ("with : " ^ string_of_int !n_input ^ " INPUT tasks ");
	print_endline ("and  : " ^ string_of_int !n_output^ " OUTPUT tasks");
	print_endline ("Constrained : PPCM     ==>" ^ string_of_int !max_ppcm );
	print_endline ("				   PERIOD   ==>" ^ string_of_int !max_period);
	print_endline ("					U 			==>" ^ string_of_float !u);

	(*** arguments parsing END ***)
		let dossier = "SysTasks" in 
		Unix.mkdir dossier 0o777;     														  				
		for j=1 to !nset do 														
			let fic="./"^(dossier)^"/setOfTask"^(string_of_int j)^".ml" in			
			let oc=open_out fic in
			let graphe=(creation_de_graphe_tache !n !l !h !n_input !n_output) in
 			if (graphe.possible!=false) then 
 			begin 
    			let gr=graphe.graph in
				let list_tasks= ref[] in
      		for j=0 to (!l)-1 do  
					for n=0 to (!h)-1 do
						if((gr.(j).(n)).id!=0) then 
         				list_tasks:=(!list_tasks)@[(gr.(j).(n))];
       			done;
       		done;
 				
 				let t_u=u_unifast !n !u in
				if(t_u.(0)!=0.0) then 
 				begin 
					let ltask= (gener_task !list_tasks t_u !max_ppcm !max_period !n) in
 					(*** PRINTING TASK PARAMETERS ***)
 					print_endline (" Generating set number " ^ string_of_int j);
 					Printf.fprintf oc "nbtasks=%d\n"(List.length ltask);
  					Printf.fprintf oc "id r C T D \n";
 					let sum_u=ref 0.0 in
  					for i=0 to (List.length ltask)-1 do
   					Printf.fprintf oc "%d %d %d %d %d \n"(List.nth ltask i).id (List.nth ltask i).firstActivation 
   					(List.nth ltask i).wcet (List.nth ltask i).period (List.nth ltask i).deadline;
     					sum_u:=(!sum_u)+.t_u.(i);
  					done;
					(*** PRINTING TASK DEPENDENCY ***)
					Printf.fprintf oc  "id:list_pred |list_succ\n";
   				for i=0 to ((List.length ltask)-1) do
    					let ta=(List.nth ltask i) in
    					Printf.fprintf oc "%d:" ta.id ;
    					(*** PRED ***)
    					for j=0 to (List.length ta.lpred)-1 do 
     						Printf.fprintf oc "%d "(List.nth ta.lpred j).id;
    					done;
    					if(ta.lpred=[]) then 
       					Printf.fprintf oc "_ ";
				     	
				     	Printf.fprintf oc  "|";
						(*** SUCC ***)
						for j=0 to (List.length ta.lsucc)-1 do 
    							Printf.fprintf oc "%d "(List.nth ta.lsucc j).id;
    					done;
    					if(ta.lsucc=[]) then 
      					Printf.fprintf oc "_ ";
      				Printf.fprintf oc "\n";
  					done;
  					print_endline (" Finished set " ^ string_of_int j);
  					(*** DONE PRINTING ***)
  					close_out oc;
				end
				else
					Printf.printf "La charge ne doit pas être supérieur au nombre de tâches!!!\n"; 
 				end
			else	
				Printf.printf "Donnez de bon paramètres pour le graphe !!!\n"; 
				Printf.printf "\n";
		done;
		u:=(!u)+.(0.05);
		;;

(*** END ***)











 
