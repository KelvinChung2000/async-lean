// Dimension-order (XY) routing logic of a router in a 4x4 mesh.
// u: the router's node (column u[1:0], row u[3:2]); d: the packet's destination.
// o: the output port: 0 = east (+1), 1 = west (-1), 2 = south (+4), 3 = north (-4).
module xy_route (input [3:0] u, input [3:0] d, output [1:0] o);
  wire xlt, xgt, ylt;
  // column of u below the column of d, and above it
  assign xlt = (~u[1] & d[1]) | (~(u[1] ^ d[1]) & ~u[0] & d[0]);
  assign xgt = (u[1] & ~d[1]) | (~(u[1] ^ d[1]) & u[0] & ~d[0]);
  // row of u below the row of d
  assign ylt = (~u[3] & d[3]) | (~(u[3] ^ d[3]) & ~u[2] & d[2]);
  // correct the column first, then the row
  assign o[0] = ~xlt & (xgt | ~ylt);
  assign o[1] = ~xlt & ~xgt;
endmodule
