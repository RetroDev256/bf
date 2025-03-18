const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

// Hopefully:

// code -> tokens
// tokens -> ast
// ast -> ir
// ir -> air
// air -> assembly
// assembly -> object file
// object file -> exe

// Currently:

// code -> tokens
// tokens -> ast
// ast -> ir
// ir -> zig code

pub fn main() !void {
    const gpa = std.heap.smp_allocator;

    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);

    const optimization_passes = 10;
    const unrolled_loops = false;

    for (args[1..]) |arg| {
        const file = try std.fs.cwd().openFile(arg, .{});
        defer file.close();

        const code = try readAll(gpa, file.reader());
        defer gpa.free(code);

        const tokens = try tokensFromCode(gpa, code);
        defer gpa.free(tokens);

        const ast = try astFromTokens(gpa, tokens);
        defer gpa.free(ast);
        defer for (ast) |node| node.free(gpa);

        var opt_ir = try irFromAst(gpa, ast);
        defer gpa.free(opt_ir);
        defer for (opt_ir) |ir| gpa.free(ir);

        for (0..optimization_passes) |_| {
            const opt_1_ir = opt_ir;
            defer gpa.free(opt_1_ir);
            defer for (opt_1_ir) |ir| gpa.free(ir);

            const opt_2_ir = try mergeShiftAdd(gpa, opt_1_ir);
            defer gpa.free(opt_2_ir);
            defer for (opt_2_ir) |ir| gpa.free(ir);

            const opt_3_ir = try combineShifts(gpa, opt_2_ir);
            defer gpa.free(opt_3_ir);
            defer for (opt_3_ir) |ir| gpa.free(ir);

            const opt_4_ir = try synthesizeClear(gpa, opt_3_ir);
            defer gpa.free(opt_4_ir);
            defer for (opt_4_ir) |ir| gpa.free(ir);

            opt_ir = try reduceLoops(gpa, opt_4_ir);
        }

        // TODO: more advanced constructions, like multiplications?

        try renderIr(opt_ir, unrolled_loops);
    }
}

// Compile program AST to zig code
fn renderIr(ir_sections: []const []const IrNode, unrolled_loops: bool) !void {
    const stdout_writer = std.io.getStdOut().writer();
    var bw = std.io.bufferedWriter(stdout_writer);
    const writer = bw.writer();

    try writer.writeAll(
        \\const std = @import("std");
        \\
        \\fn readByte() !u8 {
        \\    return error.InputUnimplemented;
        \\}
        \\
        \\fn writeByte(byte: u8) !void {
        \\    const writer = std.io.getStdOut().writer();
        \\    try writer.writeByte(byte);
        \\}
        \\
        \\pub fn main() !void {
        \\    var mem: [65536]u8 = @splat(0);
        \\    var ptr: u16 = 0;
        \\    try loop_0(&mem, &ptr);
        \\}
        \\
    );

    for (ir_sections, 0..) |ir_body, id| {
        try writer.writeAll("\n");

        if (unrolled_loops) {
            try writer.writeAll("inline ");
        }

        try writer.print("fn loop_{}(mem: *[65536]u8, ptr: *u16) !void {{\n", .{id});

        if (id == 0) {
            try renderBodyIr(writer, ir_body, 4);
        } else {
            try writer.writeByteNTimes(' ', 4);
            try writer.writeAll("while (mem[ptr.*] != 0) {\n");
            try renderBodyIr(writer, ir_body, 8);
            try writer.writeByteNTimes(' ', 4);
            try writer.writeAll("}\n");
        }

        try writer.writeAll("}\n");
    }

    try bw.flush();
}

// Compile an AST loop to zig code
fn renderBodyIr(writer: anytype, ir_body: []const IrNode, indent: usize) !void {
    for (ir_body) |node| {
        switch (node) {
            .output => |offset| {
                try writer.writeByteNTimes(' ', indent);
                try writer.writeAll("try writeByte(");
                try renderOffsetMemory(writer, offset);
                try writer.writeAll(");\n");
            },
            .input => |offset| {
                try writer.writeByteNTimes(' ', indent);
                try renderOffsetMemory(writer, offset);
                try writer.writeAll(" = try readByte();\n");
            },
            .clear => |offset| {
                try writer.writeByteNTimes(' ', indent);
                try renderOffsetMemory(writer, offset);
                try writer.writeAll(" = 0;\n");
            },
            .shift => |amt| {
                try writer.writeByteNTimes(' ', indent);
                try writer.writeAll("ptr.*");
                try renderWrapAddAssign(u16, writer, amt);
            },
            .add => |add| {
                try writer.writeByteNTimes(' ', indent);
                try renderOffsetMemory(writer, add.offset);
                try renderWrapAddAssign(u8, writer, add.addend);
            },
            .loop => |loop_index| {
                try writer.writeByteNTimes(' ', indent);
                try writer.print("try loop_{}(mem, ptr);\n", .{loop_index});
            },
        }
    }
}

fn renderOffsetMemory(writer: anytype, offset: u16) !void {
    if (offset != 0) {
        try writer.writeAll("mem[ptr.*");
        try renderWrapAdd(u16, writer, offset);
        try writer.writeByte(']');
    } else {
        try writer.writeAll("mem[ptr.*]");
    }
}

fn renderWrapAdd(comptime T: type, writer: anytype, value: T) !void {
    if (-%value < value) {
        try writer.print(" -% {}", .{-%value});
    } else {
        try writer.print(" +% {}", .{value});
    }
}

fn renderWrapAddAssign(comptime T: type, writer: anytype, value: T) !void {
    if (-%value < value) {
        try writer.print(" -%= {};\n", .{-%value});
    } else {
        try writer.print(" +%= {};\n", .{value});
    }
}

// Optimization pass - merge loop references and remove extra loops
fn reduceLoops(gpa: Allocator, ir_sections: []const []const IrNode) ![]const []const IrNode {
    var multi_ir: std.ArrayListUnmanaged([]const IrNode) = .empty;
    defer multi_ir.deinit(gpa);

    // marks what loops are redundant (deep equal), with the index of their first equal
    const redundant_loops: []?usize = try gpa.alloc(?usize, ir_sections.len);
    defer gpa.free(redundant_loops);

    compare: for (redundant_loops, 0..) |*redundancy, loop_rhs| {
        for (0..loop_rhs) |loop_lhs| {
            if (loopEqualDeep(ir_sections, loop_lhs, loop_rhs)) {
                redundancy.* = loop_lhs;
                continue :compare;
            }
        }
        redundancy.* = null;
    }

    // marks the new offsets of loops for when we remove the redundant loops
    const loop_offset: []usize = try gpa.alloc(usize, ir_sections.len);
    defer gpa.free(loop_offset);

    var cum_offset: usize = 0;
    for (redundant_loops, loop_offset) |redundant, *offset| {
        if (redundant != null) cum_offset += 1;
        offset.* = cum_offset;
    }

    relocation: for (ir_sections, 0..) |ir, ir_index| {
        var changed_ir: std.ArrayListUnmanaged(IrNode) = .empty;
        defer changed_ir.deinit(gpa);

        if (redundant_loops[ir_index] != null) {
            continue :relocation;
        } else {
            for (ir) |node| {
                switch (node) {
                    .loop => |loop_index| {
                        if (redundant_loops[loop_index]) |offset| {
                            try changed_ir.append(gpa, .{
                                .loop = offset - loop_offset[offset],
                            });
                        } else {
                            try changed_ir.append(gpa, .{
                                .loop = loop_index - loop_offset[loop_index],
                            });
                        }
                    },
                    else => try changed_ir.append(gpa, node),
                }
            }
        }

        const owned_ir = try changed_ir.toOwnedSlice(gpa);
        errdefer gpa.free(owned_ir);
        try multi_ir.append(gpa, owned_ir);
    }

    return try multi_ir.toOwnedSlice(gpa);
}

fn loopEqualDeep(ir_sections: []const []const IrNode, a: usize, b: usize) bool {
    if (ir_sections[a].len != ir_sections[b].len) {
        return false;
    }

    for (ir_sections[a], ir_sections[b]) |node_a, node_b| {
        switch (node_a) {
            .loop => |li_a| {
                if (node_b != .loop) {
                    return false;
                } else {
                    const li_b = node_b.loop;
                    if (!loopEqualDeep(ir_sections, li_a, li_b)) {
                        return false;
                    }
                }
            },
            else => if (!std.meta.eql(node_a, node_b)) {
                return false;
            },
        }
    }

    return true;
}

// Optimization pass - replace loops that contain only "add" (odd) with "clear"
fn synthesizeClear(gpa: Allocator, ir_sections: []const []const IrNode) ![]const []const IrNode {
    var multi_ir: std.ArrayListUnmanaged([]const IrNode) = .empty;
    defer multi_ir.deinit(gpa);

    // marks what loops are simply "clear the current cell", and what their offset is
    const clear_loops: []?u16 = try gpa.alloc(?u16, ir_sections.len);
    defer gpa.free(clear_loops);

    for (ir_sections, clear_loops) |ir, *clear| {
        if (ir.len == 1 and ir[0] == .add and ir[0].add.addend % 2 == 1) {
            clear.* = ir[0].add.offset;
        } else {
            clear.* = null;
        }
    }

    // marks the new offsets of loops for when we remove the clear loops
    const loop_offset: []usize = try gpa.alloc(usize, ir_sections.len);
    defer gpa.free(loop_offset);

    var cum_offset: usize = 0;
    for (clear_loops, loop_offset) |clear, *offset| {
        if (clear != null) cum_offset += 1;
        offset.* = cum_offset;
    }

    relocation: for (ir_sections, 0..) |ir, ir_index| {
        var changed_ir: std.ArrayListUnmanaged(IrNode) = .empty;
        defer changed_ir.deinit(gpa);

        if (clear_loops[ir_index] != null) {
            continue :relocation;
        } else {
            for (ir) |node| {
                switch (node) {
                    .loop => |loop_index| {
                        if (clear_loops[loop_index]) |offset| {
                            try changed_ir.append(gpa, .{
                                .clear = offset,
                            });
                        } else {
                            try changed_ir.append(gpa, .{
                                .loop = loop_index - loop_offset[loop_index],
                            });
                        }
                    },
                    else => try changed_ir.append(gpa, node),
                }
            }
        }

        const owned_ir = try changed_ir.toOwnedSlice(gpa);
        errdefer gpa.free(owned_ir);
        try multi_ir.append(gpa, owned_ir);
    }

    return try multi_ir.toOwnedSlice(gpa);
}

// Optimization pass - merge consecutive shifts and adds and clears
// into one shift and multiple adds and multiple clears
fn combineShifts(gpa: Allocator, ir_sections: []const []const IrNode) ![]const []const IrNode {
    var multi_ir: std.ArrayListUnmanaged([]const IrNode) = .empty;
    defer multi_ir.deinit(gpa);

    for (ir_sections) |ir| {
        var changed_ir: std.ArrayListUnmanaged(IrNode) = .empty;
        defer changed_ir.deinit(gpa);

        var index: usize = 0;
        while (index < ir.len) {
            switch (ir[index]) {
                .output, .input, .clear, .shift, .add => {
                    const offset_ir = ir[index..];
                    const range = prefixedNonLoopCount(offset_ir);
                    const combine_ir = offset_ir[0..range];

                    const cum_shift = cumulativeShift(combine_ir);
                    if (cum_shift != 0) {
                        try changed_ir.append(gpa, .{ .shift = cum_shift });
                    }

                    var loc_shift: u16 = 0;
                    for (combine_ir) |node| {
                        const delta_shift = loc_shift -% cum_shift;
                        switch (node) {
                            .output => |offset| {
                                try changed_ir.append(gpa, .{ .output = offset +% delta_shift });
                            },
                            .input => |offset| {
                                try changed_ir.append(gpa, .{ .input = offset +% delta_shift });
                            },
                            .clear => |offset| {
                                try changed_ir.append(gpa, .{ .clear = offset +% delta_shift });
                            },
                            .add => |add| {
                                try changed_ir.append(gpa, .{ .add = .{
                                    .addend = add.addend,
                                    .offset = add.offset +% delta_shift,
                                } });
                            },
                            .shift => |amt| loc_shift +%= amt,
                            else => unreachable,
                        }
                    }

                    index += range;
                },
                .loop => {
                    try changed_ir.append(gpa, ir[index]);
                    index += 1;
                },
            }
        }

        const owned_ir = try changed_ir.toOwnedSlice(gpa);
        errdefer gpa.free(owned_ir);
        try multi_ir.append(gpa, owned_ir);
    }

    return try multi_ir.toOwnedSlice(gpa);
}

fn cumulativeShift(ir: []const IrNode) u16 {
    var cum_shift: u16 = 0;
    for (ir) |node| {
        switch (node) {
            .shift => |amt| cum_shift +%= amt,
            else => {},
        }
    }
    return cum_shift;
}

fn prefixedNonLoopCount(ir: []const IrNode) usize {
    var index: usize = 0;
    while (index < ir.len) : (index += 1) {
        if (ir[index] == .loop) break;
    }
    return index;
}

// Optimization pass - combine consecutive adds, combine consecutive shifts
fn mergeShiftAdd(gpa: Allocator, ir_sections: []const []const IrNode) ![]const []const IrNode {
    var multi_ir: std.ArrayListUnmanaged([]const IrNode) = .empty;
    defer multi_ir.deinit(gpa);

    for (ir_sections) |ir| {
        var changed_ir: std.ArrayListUnmanaged(IrNode) = .empty;
        defer changed_ir.deinit(gpa);

        var index: usize = 0;
        while (index < ir.len) : (index += 1) {
            switch (ir[index]) {
                .add => |head_add| {
                    var cum_add: u8 = head_add.addend;
                    combine: while (index + 1 < ir.len) : (index += 1) {
                        switch (ir[index + 1]) {
                            .add => |sub_add| {
                                if (sub_add.offset != head_add.offset) {
                                    break :combine;
                                } else {
                                    cum_add +%= sub_add.addend;
                                }
                            },
                            else => break :combine,
                        }
                    }
                    try changed_ir.append(gpa, .{
                        .add = .{ .addend = cum_add, .offset = head_add.offset },
                    });
                },
                .shift => |head_shift| {
                    var cum_shift: u16 = head_shift;
                    combine: while (index + 1 < ir.len) : (index += 1) {
                        switch (ir[index + 1]) {
                            .shift => |sub_shift| cum_shift +%= sub_shift,
                            else => break :combine,
                        }
                    }
                    if (cum_shift != 0) {
                        try changed_ir.append(gpa, .{ .shift = cum_shift });
                    }
                },
                else => try changed_ir.append(gpa, ir[index]),
            }
        }

        const owned_ir = try changed_ir.toOwnedSlice(gpa);
        errdefer gpa.free(owned_ir);
        try multi_ir.append(gpa, owned_ir);
    }

    return try multi_ir.toOwnedSlice(gpa);
}

// Similar to AstNode, but provides extra elements for optimization passes
const IrNode = union(enum) {
    output: u16, // u16: pointer offset
    input: u16, // u16: pointer offset
    clear: u16, // u16: pointer offset
    shift: u16, // u16: shift amount
    add: struct {
        offset: u16, // u16: pointer offset
        addend: u8, // u8: add amount
    },
    loop: usize, // usize: index of loop in ir sections
};

fn irFromAst(gpa: Allocator, root_ast: []const AstNode) ![]const []const IrNode {
    // ast of loops that we still need to process
    var multi_ast: std.ArrayListUnmanaged([]const AstNode) = .empty;
    defer multi_ast.deinit(gpa);
    try multi_ast.append(gpa, root_ast);

    // ir of processed loops
    var multi_ir: std.ArrayListUnmanaged([]const IrNode) = .empty;
    defer multi_ir.deinit(gpa);

    while (multi_ast.pop()) |ast| {
        var ir: std.ArrayListUnmanaged(IrNode) = .empty;
        defer ir.deinit(gpa);

        for (ast) |node| {
            switch (node) {
                .output => try ir.append(gpa, .{ .output = 0 }),
                .input => try ir.append(gpa, .{ .input = 0 }),
                .decrement => try ir.append(gpa, .{ .add = .{ .addend = 255, .offset = 0 } }),
                .increment => try ir.append(gpa, .{ .add = .{ .addend = 1, .offset = 0 } }),
                .left_shift => try ir.append(gpa, .{ .shift = 65535 }),
                .right_shift => try ir.append(gpa, .{ .shift = 1 }),
                .loop => |loop_ast| {
                    try multi_ast.insert(gpa, 0, loop_ast);
                    const loop_index = multi_ast.items.len + multi_ir.items.len;
                    try ir.append(gpa, .{ .loop = loop_index });
                },
            }
        }

        const owned_ir = try ir.toOwnedSlice(gpa);
        errdefer gpa.free(owned_ir);
        try multi_ir.append(gpa, owned_ir);
    }

    return try multi_ir.toOwnedSlice(gpa);
}

// Similar to Token, but it abstracts loops
const AstNode = union(enum) {
    output,
    input,
    decrement,
    increment,
    left_shift,
    right_shift,
    loop: []const AstNode,

    fn free(self: *const @This(), gpa: Allocator) void {
        switch (self.*) {
            .loop => |nodes| {
                for (nodes) |node| {
                    node.free(gpa);
                }
                gpa.free(nodes);
            },
            else => {},
        }
    }
};

// Form an abstract syntax tree from tokens (essentially, nest loops)
fn astFromTokens(gpa: Allocator, tokens: []const Token) ![]const AstNode {
    var root_list: std.ArrayListUnmanaged(AstNode) = .empty;
    errdefer root_list.deinit(gpa);
    errdefer for (root_list.items) |node| node.free(gpa);

    var index: usize = 0;
    while (index < tokens.len) : (index += 1) {
        switch (tokens[index]) {
            .output => try root_list.append(gpa, .output),
            .input => try root_list.append(gpa, .input),
            .decrement => try root_list.append(gpa, .decrement),
            .increment => try root_list.append(gpa, .increment),
            .left_shift => try root_list.append(gpa, .left_shift),
            .right_shift => try root_list.append(gpa, .right_shift),
            .open_loop => {
                const end_offset = try findLoopClose(tokens[index..]);
                const loop_tokens = tokens[index..][1..end_offset];
                const loop = try astFromTokens(gpa, loop_tokens);
                errdefer gpa.free(loop);
                errdefer for (loop) |node| node.free(gpa);
                try root_list.append(gpa, .{ .loop = loop });
                index += end_offset;
            },
            .close_loop => return error.UnexpectedLoopClose,
        }
    }

    return try root_list.toOwnedSlice(gpa);
}

fn findLoopClose(tokens: []const Token) !usize {
    var loops: usize = 0;
    search: for (tokens, 0..) |token, index| {
        switch (token) {
            .open_loop => loops += 1,
            .close_loop => loops -= 1,
            else => continue :search,
        }
        if (loops == 0) {
            return index;
        }
    }
    return error.MissingLoopClose;
}

// . , - + < > [ ]
const Token = enum {
    output,
    input,
    decrement,
    increment,
    left_shift,
    right_shift,
    open_loop,
    close_loop,
};

// Tokenize a file
fn tokensFromCode(gpa: Allocator, code: []const u8) ![]const Token {
    var tokens: std.ArrayListUnmanaged(Token) = .empty;
    errdefer tokens.deinit(gpa);

    for (code) |byte| switch (byte) {
        '.' => try tokens.append(gpa, .output),
        ',' => try tokens.append(gpa, .input),
        '-' => try tokens.append(gpa, .decrement),
        '+' => try tokens.append(gpa, .increment),
        '<' => try tokens.append(gpa, .left_shift),
        '>' => try tokens.append(gpa, .right_shift),
        '[' => try tokens.append(gpa, .open_loop),
        ']' => try tokens.append(gpa, .close_loop),
        else => {},
    };

    return try tokens.toOwnedSlice(gpa);
}

// Read an entire file into memory
fn readAll(gpa: Allocator, reader: anytype) ![]const u8 {
    var bytes: std.ArrayListUnmanaged(u8) = .empty;
    errdefer bytes.deinit(gpa);

    var read_total: usize = 0;
    while (true) {
        try bytes.ensureTotalCapacity(gpa, read_total + 1);
        bytes.items.len = bytes.capacity;

        const read_amt = try reader.read(bytes.items[read_total..]);
        read_total += read_amt;

        if (read_amt == 0) {
            bytes.items.len = read_total;
            return try bytes.toOwnedSlice(gpa);
        }
    }
}

// Write a string of bytes to a file
fn writeAll(writer: anytype, bytes: []const u8) !void {
    var index: usize = 0;
    while (index < bytes.len) {
        index += try writer.write(bytes[index..]);
    }
}
