set boxwidth 1 absolute
set style fill solid 2.00 border -1
set style data histogram
set style histogram cluster gap 5
set xtics 1000 nomirror
set ytics 0.1 nomirror
set yrange [0.1:1]
set mxtics 4
set mytics 4
set ytics 0.1
set ylabel "Sucess Ratio"
set xlabel "Load of task system"
set term jpeg;set output "histoSuccessRatio.jpeg";plot './histogrammeSucessRatio.ml' using 2 t "Exact Algorithm", '' using 3 t "Proposed heuristic", '' using 4 t "Worst-Fit heuristic", '' using 5:xtic(1) t "Best-Fit heuristic";

set logscale y 10;
