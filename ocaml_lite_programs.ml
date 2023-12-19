let add x y = x + y;;
let absolute_value x = if x < 0 then - x else x;;

type day =
 | Monday
 | Tuesday
 | Wednesday
 | Thursday
 | Friday
 | Saturday
 | Sunday;;

let weekday (w : day) : bool =
    match w with
    | Saturday -> false
    | Sunday -> false
    | _ -> true;;

type int_option =
 | Hasint of int
 | Noint;;

let default (i : int) (o : int_option) : int =
    match o with
    | Hasint vl -> vl
    | Noint -> i;;

let test_day = weekday Monday;;

let test_weekend = weekday Saturday;;

let test_default = default 1 (Hasint 2);;

let test_default_2 = default 1 (Noint);;
