// A self-timed ring of five C-elements, each with an inverted feedback input.
// The circuit is closed: every signal is driven by a gate.  Stage 0 is observable (an
// output port); the other stages are internal wires.
module ring5 (output c0);
  wire c1, c2, c3, c4;
  assign c0 = c4 & ~c1 | c0 & (c4 | ~c1);
  assign c1 = c0 & ~c2 | c1 & (c0 | ~c2);
  assign c2 = c1 & ~c3 | c2 & (c1 | ~c3);
  assign c3 = c2 & ~c4 | c3 & (c2 | ~c4);
  assign c4 = c3 & ~c0 | c4 & (c3 | ~c0);
endmodule
// async-lean init: c0=1 c1=0 c2=0 c3=0 c4=0
