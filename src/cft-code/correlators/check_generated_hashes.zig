const std = @import("std");

const prefix = "// source-hash ";

fn hashBytes(bytes: []const u8) u32 {
    var hash: u32 = 0x811c9dc5;
    for (bytes) |byte| {
        hash = (hash ^ @as(u32, byte)) *% 0x01000193;
    }
    return hash;
}

fn hexDigit(value: u4) u8 {
    const byte: u8 = @intCast(value);
    return if (byte < 10) '0' + byte else 'A' + (byte - 10);
}

fn formatHash(hash: u32) [8]u8 {
    var out: [8]u8 = undefined;
    var shift: u5 = 28;
    for (&out) |*byte| {
        byte.* = hexDigit(@intCast((hash >> shift) & 0xf));
        shift -%= 4;
    }
    return out;
}

fn readFileAlloc(io: std.Io, allocator: std.mem.Allocator, path: []const u8) ![]u8 {
    return std.Io.Dir.cwd().readFileAlloc(io, path, allocator, .limited(16 * 1024 * 1024));
}

fn checkGeneratedFile(io: std.Io, allocator: std.mem.Allocator, generated_path: []const u8) !void {
    const generated = try readFileAlloc(io, allocator, generated_path);
    defer allocator.free(generated);

    var saw_manifest = false;
    var lines = std.mem.splitScalar(u8, generated, '\n');
    while (lines.next()) |line| {
        if (!std.mem.startsWith(u8, line, prefix)) continue;
        saw_manifest = true;
        const row = line[prefix.len..];
        const space = std.mem.indexOfScalar(u8, row, ' ') orelse return error.InvalidSourceHashManifest;
        const source_path = row[0..space];
        const recorded_hash = row[space + 1 ..];
        if (recorded_hash.len != 8) return error.InvalidSourceHashManifest;

        const source = try readFileAlloc(io, allocator, source_path);
        defer allocator.free(source);
        const actual_hash = formatHash(hashBytes(source));
        if (!std.mem.eql(u8, recorded_hash, &actual_hash)) {
            std.debug.print(
                "Generated CFT sources are stale: {s} records {s} for {s}, actual {s}. Run `zig build regen`.\n",
                .{ generated_path, recorded_hash, source_path, actual_hash },
            );
            return error.StaleGeneratedSource;
        }
    }
    if (!saw_manifest) {
        std.debug.print(
            "Generated CFT file {s} has no source-hash manifest. Run `zig build regen`.\n",
            .{generated_path},
        );
        return error.MissingSourceHashManifest;
    }
}

pub fn main(init: std.process.Init) !void {
    const io = init.io;
    const allocator = init.arena.allocator();
    const args = try init.minimal.args.toSlice(allocator);
    var count: usize = 0;
    for (args[1..]) |path| {
        count += 1;
        try checkGeneratedFile(io, allocator, path);
    }
    if (count == 0) return error.MissingGeneratedFileArgument;
}
