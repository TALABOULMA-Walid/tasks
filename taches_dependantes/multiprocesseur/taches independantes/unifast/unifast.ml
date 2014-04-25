(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
let unifast(n,u_t)=
 let sumU = ref u_t in 
 let u_verif= ref 0.0 in
   for i=1 to (n-1) do

     let nextSumU =ref ((!sumU) *. ((Random.float 1.0) ** (1.0/. (float_of_int (n-i))))) in  
     let vectU_i= ref (((!sumU) -. (!nextSumU))) in
     while !vectU_i > 1.0 do 
       nextSumU := (!sumU) *. ((Random.float 1.0) ** (1.0/. (float_of_int (n-i))) );  
       vectU_i := ((!sumU) -. (!nextSumU) );
     done;

      Printf.printf "U%d= %f \n" i  !vectU_i;
      sumU := (!nextSumU);
      u_verif:=(!u_verif)+.(!vectU_i) ;
   done;
      sumU:=u_t-.(!u_verif) ;
      Printf.printf "U%d= %f\n" n (!u_verif);
      (!u_verif +. (!sumU));;
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
let main=
let u=unifast(30,15.0) in
 Printf.printf "U= %f\n" u;;


