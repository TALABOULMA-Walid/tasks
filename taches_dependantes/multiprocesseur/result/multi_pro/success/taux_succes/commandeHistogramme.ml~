set boxwidth 1 absolute
set style fill solid 2.00 border -1
set style data histogram
set style histogram cluster gap 3
set xtics 1000 nomirror
set ytics 0.1 nomirror
set yrange [0:1]
set mxtics 2
set mytics 2
set ytics 0.1
set encoding iso_8859_1;
set ylabel "Taux de succ\350s "
set xlabel "Moyennes des facteurs d\264utilisation des ensembles de t\342ches"
set term jpeg;set output "histoSuccessRatio.jpeg"; 
plot './histo.ml' using 2 t "Heuristique propos\351e", '' using 3:xtic(1) t "Branch and Bound";


set logscale y 10;
