const std = @import("std");
const fixtures = @import("generated_fixtures.zig");
const kernel = @import("../kernel.zig");

const allocator = std.heap.c_allocator;

/// TheoryId selects one generated fixture through the generic ABI.
pub const TheoryId = enum(u32) {
    free_fermion = 1,
    eta_xi_sphere = 2,
    eta_xi_torus = 3,
    bc = 4,
    free_boson = 5,
};

pub const first_theory_id = TheoryId.free_fermion;

pub const ContextTag = union(TheoryId) {
    free_fermion: *fixtures.FreeFermion.Context,
    eta_xi_sphere: *fixtures.EtaXiSphere.Context,
    eta_xi_torus: *fixtures.EtaXiTorus.Context,
    bc: *fixtures.Bc.Context,
    free_boson: *fixtures.FreeBoson.Context,

    pub fn create(id: TheoryId) !ContextTag {
        return switch (id) {
            .free_fermion => .{ .free_fermion = try fixtures.FreeFermion.contextCreate(allocator) },
            .eta_xi_sphere => .{ .eta_xi_sphere = try fixtures.EtaXiSphere.contextCreate(allocator) },
            .eta_xi_torus => .{ .eta_xi_torus = try fixtures.EtaXiTorus.contextCreate(allocator) },
            .bc => .{ .bc = try fixtures.Bc.contextCreate(allocator) },
            .free_boson => .{ .free_boson = try fixtures.FreeBoson.contextCreate(allocator) },
        };
    }

    pub fn destroy(self: ContextTag) void {
        switch (self) {
            .free_fermion => |inner| fixtures.FreeFermion.contextDestroy(inner),
            .eta_xi_sphere => |inner| fixtures.EtaXiSphere.contextDestroy(inner),
            .eta_xi_torus => |inner| fixtures.EtaXiTorus.contextDestroy(inner),
            .bc => |inner| fixtures.Bc.contextDestroy(inner),
            .free_boson => |inner| fixtures.FreeBoson.contextDestroy(inner),
        }
    }

    pub fn symbolIntern(self: ContextTag, name: []const u8) !u32 {
        return switch (self) {
            .free_fermion => |inner| fixtures.FreeFermion.symbolIntern(inner, name),
            .eta_xi_sphere => |inner| fixtures.EtaXiSphere.symbolIntern(inner, name),
            .eta_xi_torus => |inner| fixtures.EtaXiTorus.symbolIntern(inner, name),
            .bc => |inner| fixtures.Bc.symbolIntern(inner, name),
            .free_boson => |inner| fixtures.FreeBoson.symbolIntern(inner, name),
        };
    }

    pub fn fieldInsert(self: ContextTag, field_id: u16, coords: []const u32, labels: []const u32) !void {
        switch (self) {
            .free_fermion => |inner| try fixtures.FreeFermion.fieldInsert(inner, field_id, coords, labels),
            .eta_xi_sphere => |inner| try fixtures.EtaXiSphere.fieldInsert(inner, field_id, coords, labels),
            .eta_xi_torus => |inner| try fixtures.EtaXiTorus.fieldInsert(inner, field_id, coords, labels),
            .bc => |inner| try fixtures.Bc.fieldInsert(inner, field_id, coords, labels),
            .free_boson => |inner| try fixtures.FreeBoson.fieldInsert(inner, field_id, coords, labels),
        }
    }

    pub fn normalOrdering(self: ContextTag, field_count: usize) !void {
        switch (self) {
            .free_fermion => |inner| try fixtures.FreeFermion.normalOrdering(inner, field_count),
            .eta_xi_sphere => |inner| try fixtures.EtaXiSphere.normalOrdering(inner, field_count),
            .eta_xi_torus => |inner| try fixtures.EtaXiTorus.normalOrdering(inner, field_count),
            .bc => |inner| try fixtures.Bc.normalOrdering(inner, field_count),
            .free_boson => |inner| try fixtures.FreeBoson.normalOrdering(inner, field_count),
        }
    }

    pub fn freeze(self: ContextTag) !kernel.Call.MultiOp {
        return switch (self) {
            .free_fermion => |inner| fixtures.FreeFermion.operatorListFreeze(inner),
            .eta_xi_sphere => |inner| fixtures.EtaXiSphere.operatorListFreeze(inner),
            .eta_xi_torus => |inner| fixtures.EtaXiTorus.operatorListFreeze(inner),
            .bc => |inner| fixtures.Bc.operatorListFreeze(inner),
            .free_boson => |inner| fixtures.FreeBoson.operatorListFreeze(inner),
        };
    }

    pub fn count(self: ContextTag, ops: kernel.Call.MultiOp) !usize {
        return switch (self) {
            .free_fermion => fixtures.FreeFermion.correlatorCount(ops),
            .eta_xi_sphere => fixtures.EtaXiSphere.correlatorCount(ops),
            .eta_xi_torus => fixtures.EtaXiTorus.correlatorCount(ops),
            .bc => fixtures.Bc.correlatorCount(ops),
            .free_boson => fixtures.FreeBoson.correlatorCount(ops),
        };
    }

    pub fn run(self: ContextTag, ops: kernel.Call.MultiOp, state: anytype, thunk: anytype) !void {
        switch (self) {
            .free_fermion => try fixtures.FreeFermion.correlatorRun(ops, state, thunk),
            .eta_xi_sphere => try fixtures.EtaXiSphere.correlatorRun(ops, state, thunk),
            .eta_xi_torus => try fixtures.EtaXiTorus.correlatorRun(ops, state, thunk),
            .bc => try fixtures.Bc.correlatorRun(ops, state, thunk),
            .free_boson => try fixtures.FreeBoson.correlatorRun(ops, state, thunk),
        }
    }

};

pub fn scalarAtomParameterName(id: TheoryId, atom: u32) ?[]const u8 {
    return switch (id) {
        .free_fermion => fixtures.FreeFermion.scalarAtomParameterName(atom),
        .eta_xi_sphere => fixtures.EtaXiSphere.scalarAtomParameterName(atom),
        .eta_xi_torus => fixtures.EtaXiTorus.scalarAtomParameterName(atom),
        .bc => fixtures.Bc.scalarAtomParameterName(atom),
        .free_boson => fixtures.FreeBoson.scalarAtomParameterName(atom),
    };
}

pub fn theoryId(raw: u32) !TheoryId {
    return switch (raw) {
        1 => .free_fermion,
        2 => .eta_xi_sphere,
        3 => .eta_xi_torus,
        4 => .bc,
        5 => .free_boson,
        else => error.UnknownTheory,
    };
}

pub fn theoryHash(id: TheoryId) u32 {
    return switch (id) {
        .free_fermion => fixtures.FreeFermion.theoryHash(),
        .eta_xi_sphere => fixtures.EtaXiSphere.theoryHash(),
        .eta_xi_torus => fixtures.EtaXiTorus.theoryHash(),
        .bc => fixtures.Bc.theoryHash(),
        .free_boson => fixtures.FreeBoson.theoryHash(),
    };
}
