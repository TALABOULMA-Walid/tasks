type TasksSet =
{mutable listTasks : list Task;
 mutable load : float;
 mutable ppcm : float;
 mutable schedulable : bool; 
}
and Task =
{id : int ;
 mutable firstActivation :int;
 wcet : int;
 period: int;
 deadline: int;
 mutable pred : list int;
 mutable succ : list int;
}