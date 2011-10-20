signature ANSI =
  sig
    type color
    type full_color = color * bool
    val black : color
    val red : color
    val green : color
    val yellow : color
    val blue : color
    val magenta : color
    val cyan : color
    val white : color
    val dark_black : full_color
    val dark_red : full_color
    val dark_green : full_color
    val dark_yellow : full_color
    val dark_blue : full_color
    val dark_magenta : full_color
    val dark_cyan : full_color
    val dark_white : full_color
    val dark_gray : full_color
    val bright_red : full_color
    val bright_green : full_color
    val bright_yellow : full_color
    val bright_blue : full_color
    val bright_magenta : full_color
    val bright_cyan : full_color
    val bright_white : full_color
    val reset : string
    val underline : bool -> string
    val bold : bool -> string
    val buildColor : full_color -> string
    val colorStr : string -> full_color -> string
  end


structure Ansi (*:> ANSI*) =
struct
  (* Control Sequence Introducer *)
  val CSI = "\^[["

  (* Send a one argument command *)
  fun cmd1 s n = CSI ^ (Int.toString n) ^ s
  (* Send a two argument command *)
  fun cmd2 s (n, m) = CSI ^ (Int.toString n) ^ ";" ^ (Int.toString m) ^ s

  (* Send a "Select Graphic Rendition" command *)
  val SGR = cmd1 "m"

  type color = int
  type full_color = color * bool

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
 
  fun fgColor color = SGR (30 + color) 
  fun bgColor color = SGR (40 + color)
  val defaultFgColor = SGR 39
  val defaultBgColor = SGR 40

  fun fullColor (color, is_bold) =
      bold is_bold ^ fgColor color
  fun colorStr s color = fullColor color ^ s ^ reset

  type clear = int
  val (Forward, Backward, Full) = (0, 1, 2)
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

  fun cursorVisible true = CSI ^ "?25l"
    | cursorVisible false = CSI ^ "?25h"
end
