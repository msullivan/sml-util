signature ANSI =
  sig
    type color
    val dark_black : color
    val dark_red : color
    val dark_green : color
    val dark_yellow : color
    val dark_blue : color
    val dark_magenta : color
    val dark_cyan : color
    val dark_white : color
    val dark_gray : color
    val bright_red : color
    val bright_green : color
    val bright_yellow : color
    val bright_blue : color
    val bright_magenta : color
    val bright_cyan : color
    val bright_white : color

    val defaultFgColor : string
    val defaultBgColor : string
    val fgColor : color -> string
    val bgColor : color -> string
    val colorStr : string -> color -> color -> string

    val reset : string
    val underline : bool -> string
    val bold : bool -> string
    val blink : bool -> string
    val inverse : bool -> string
    val cursorUp : int -> string
    val cursorDown : int -> string
    val cursorForward : int -> string
    val cursorBack : int -> string
    val cursorNextLine : int -> string
    val cursorPrevLine : int -> string
    val cursorSetCol : int -> string
    val cursorPosition : int * int -> string
    val cursorVisible : bool -> string
    val clearScreen : int -> string
    val clearLine : int -> string
    val scrollUp : int -> string
    val scrollDown : int -> string
  end


structure Ansi :> ANSI =
struct
  (* Control Sequence Introducer: Miami *)
  val CSI = "\^[["

  (* Send a one argument command *)
  fun cmd1 s n = CSI ^ (Int.toString n) ^ s
  (* Send a two argument command *)
  fun cmd2 s (n, m) = CSI ^ (Int.toString n) ^ ";" ^ (Int.toString m) ^ s

  (* Send a "Select Graphic Rendition" command *)
  val SGR = cmd1 "m"

  type half_color = int
  type color = half_color * bool

  val (black, red, green, yellow, blue, magenta, cyan, white) =
      (0, 1, 2, 3, 4, 5, 6, 7)
  val (dark_black, dark_red, dark_green, dark_yellow,
       dark_blue, dark_magenta, dark_cyan, dark_white) =
      ((black, false), (red, false), (green, false), (yellow, false),
       (blue, false), (magenta, false), (cyan, false), (white, false))
  val (dark_gray, bright_red, bright_green, bright_yellow,
       bright_blue, bright_magenta, bright_cyan, bright_white) =
      ((black, true), (red, true), (green, true), (yellow, true),
       (blue, true), (magenta, true), (cyan, true), (white, true))

  val reset = SGR 0
  fun underline true = SGR 4
    | underline false = SGR 24
  fun bold true = SGR 1
    | bold false = SGR 22
  fun blink true = SGR 5
    | blink false = SGR 25
  fun inverse true = SGR 7
    | inverse false = SGR 27
  fun cursorVisible true = CSI ^ "?25l"
    | cursorVisible false = CSI ^ "?25h"
 
  fun fgOffset half_color = SGR (30 + half_color)
  fun bgOffset half_color = SGR (40 + half_color)
  val defaultFgColor = SGR 39
  val defaultBgColor = SGR 40

  fun fgColor (half_color, is_bold) = bold is_bold ^ fgOffset half_color
  fun bgColor (half_color, _) = bgOffset half_color
  fun colorStr s fg bg = fgColor fg ^ bgColor bg ^ s ^ reset

  val cursorUp = cmd1 "A"
  val cursorDown = cmd1 "B"
  val cursorForward = cmd1 "C"
  val cursorBack = cmd1 "D"
  val cursorNextLine = cmd1 "E"
  val cursorPrevLine = cmd1 "F"
  val cursorSetCol = cmd1 "G"
  val cursorPosition = cmd2 "H"
  val clearScreen = cmd1 "J"
  val clearLine = cmd1 "K"
  val scrollUp = cmd1 "S"
  val scrollDown = cmd1 "T"
end
