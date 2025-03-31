const builtin = @import("builtin");
const std = @import("std");
const assert = std.debug.assert;
const mem = std.mem;
const math = std.math;
const crypto = std.crypto;
const Allocator = std.mem.Allocator;
const ArrayListUnmanaged = std.ArrayListUnmanaged;
const ArrayList = std.ArrayListUnmanaged;

pub const AllocErrorBehavior = enum {
    ALLOCATION_ERRORS_RETURN_ERROR,
    ALLOCATION_ERRORS_PANIC,
    ALLOCATION_ERRORS_ARE_UNREACHABLE,
};

pub const GrowthModel = enum {
    GROW_EXACT_NEEDED,
    GROW_EXACT_NEEDED_WITH_ATOMIC_PADDING,
    GROW_BY_100_PERCENT,
    GROW_BY_100_PERCENT_WITH_ATOMIC_PADDING,
    GROW_BY_50_PERCENT,
    GROW_BY_50_PERCENT_WITH_ATOMIC_PADDING,
    GROW_BY_25_PERCENT,
    GROW_BY_25_PERCENT_WITH_ATOMIC_PADDING,
};

pub const ListOptions = struct {
    element_type: type,
    allocator: *const Allocator,
    alignment: ?u29 = null,
    alloc_error_behavior: AllocErrorBehavior = .ALLOCATION_ERRORS_PANIC,
    growth_model: GrowthModel = .GROW_BY_50_PERCENT_WITH_ATOMIC_PADDING,
    index_type: type = usize,
    secure_wipe_bytes: bool = false,
};

pub fn define_list_type(comptime options: ListOptions) type {
    const opt = comptime check: {
        var opts = options;
        if (opts.alignment) |a| {
            if (a == @alignOf(opts.T)) {
                opts.alignment = null;
            }
        }
        break :check opts;
    };
    if (opt.alignment) |a| {
        if (!math.isPowerOfTwo(a)) @panic("alignment must be a power of 2");
    }
    return struct {
        ptr: Ptr = UNINIT_PTR,
        len: Idx = 0,
        cap: Idx = 0,

        pub const T: type = opt.element_type;
        pub const Idx: type = opt.index_type;
        pub const Ptr: type = if (ALIGN) |a| [*]align(a) T else [*]T;
        pub const Error = Allocator.Error;
        pub const Slice = if (ALIGN) |a| ([]align(a) T) else []T;
        pub fn SentinelSlice(comptime sentinel: T) type {
            return if (ALIGN) |a| ([:sentinel]align(a) T) else [:sentinel]T;
        }
        pub const ALLOC: *const Allocator = opt.allocator;
        pub const EMPTY = List{
            .ptr = UNINIT_PTR,
            .len = 0,
            .cap = 0,
        };
        const List = @This();
        const ALLOC_ERROR_BEHAVIOR = opt.alloc_error_behavior;
        const ALIGN = opt.alignment;
        const GROWTH = opt.growth_model;
        const RETURN_ERRORS = opt.alloc_error_behavior == .ALLOCATION_ERRORS_RETURN_ERROR;
        const SECURE_WIPE = opt.secure_wipe_bytes;
        const UNINIT_PTR: Ptr = if (ALIGN) |a| mem.alignBackward(Idx, math.maxInt(Idx), @intCast(a)) else mem.alignBackward(Idx, math.maxInt(Idx), @alignOf(T));

        pub fn slice(self: List) Slice {
            return self.ptr[0..self.len];
        }

        pub fn array_window(self: List, start: Idx, comptime length: Idx) *[length]T {
            assert(start + length <= self.len);
            return self.ptr[start..self.len][0..length];
        }

        pub fn slice_with_sentinel(self: List, comptime sentinel: T) SentinelSlice(T) {
            assert(self.len < self.cap);
            self.ptr[self.len] = sentinel;
            return self.ptr[0..self.len :sentinel];
        }

        pub fn slice_full_capacity(self: List) Slice {
            return self.ptr[0..self.cap];
        }

        pub fn slice_unused_capacity(self: List) []T {
            return self.ptr[self.len..self.cap];
        }

        pub fn set_len(self: *List, new_len: usize) void {
            assert(new_len <= self.cap);
            if (SECURE_WIPE and new_len < self.len) {
                crypto.secureZero(T, self.ptr[new_len..self.len]);
            }
            self.len = new_len;
        }

        pub fn new_empty() List {
            return List{};
        }

        pub fn new_with_capacity(capacity: Idx) if (RETURN_ERRORS) Error!List else List {
            var self = List{};
            if (RETURN_ERRORS) {
                try self.ensure_total_capacity_exact(capacity);
            } else {
                self.ensure_total_capacity_exact(capacity);
            }
            return self;
        }

        pub fn clone(self: List) if (RETURN_ERRORS) Error!List else List {
            var new_list = if (RETURN_ERRORS) try List.new_with_capacity(self.cap) else List.new_with_capacity(self.cap);
            new_list.append_slice_assume_capacity(self.ptr[0..self.len]);
            return new_list;
        }

        pub fn to_owned_slice(self: *List) if (RETURN_ERRORS) Error!Slice else Slice {
            const old_memory = self.ptr[0..self.cap];
            if (ALLOC.remap(old_memory, self.len)) |new_items| {
                self.* = EMPTY;
                return new_items;
            }
            const new_memory = ALLOC.alignedAlloc(T, ALIGN, self.len) catch |err| return handle_alloc_error(err);
            @memcpy(new_memory, self.ptr[0..self.len]);
            self.clear_and_free();
            return new_memory;
        }

        pub fn to_owned_slice_sentinel(self: *List, comptime sentinel: T) if (RETURN_ERRORS) Error!SentinelSlice(sentinel) else SentinelSlice(sentinel) {
            if (RETURN_ERRORS) {
                try self.ensure_total_capacity_exact(self.len + 1);
            } else {
                self.ensure_total_capacity_exact(self.len + 1);
            }
            self.append_assume_capacity(sentinel);
            const result: Slice = if (RETURN_ERRORS) try self.to_owned_slice() else self.to_owned_slice();
            return result[0 .. result.len - 1 :sentinel];
        }

        pub fn from_owned_slice(from_slice: Slice) List {
            return List{
                .ptr = from_slice.ptr,
                .len = from_slice.len,
                .cap = from_slice.len,
            };
        }

        pub fn from_owned_slice_sentinel(comptime sentinel: T, from_slice: [:sentinel]T) List {
            return List{
                .ptr = from_slice.ptr,
                .len = from_slice.len,
                .cap = from_slice.len + 1,
            };
        }

        pub fn insert_slot(self: *List, idx: Idx) if (RETURN_ERRORS) Error!*T else *T {
            if (RETURN_ERRORS) {
                try self.ensure_unused_capacity(1);
            } else {
                self.ensure_unused_capacity(1);
            }
            return self.insert_slot_assume_capacity(idx);
        }

        pub fn insert_slot_assume_capacity(self: *List, idx: Idx) *T {
            assert(idx <= self.len);
            mem.copyBackwards(T, self.ptr[idx + 1 .. self.len + 1], self.ptr[idx..self.len]);
            return self.ptr + idx;
        }

        pub fn insert(self: *List, idx: Idx, item: T) if (RETURN_ERRORS) Error!void else void {
            const ptr = if (RETURN_ERRORS) try self.insert_slot(idx) else self.insert_slot(idx);
            ptr.* = item;
        }

        pub fn insert_assume_capacity(self: *List, idx: Idx, item: T) void {
            const ptr = self.insert_slot_assume_capacity(idx);
            ptr.* = item;
        }

        pub fn insert_many_slots(self: *List, idx: Idx, count: Idx) if (RETURN_ERRORS) Error![]T else []T {
            if (RETURN_ERRORS) {
                try self.ensure_unused_capacity(count);
            } else {
                self.ensure_unused_capacity(count);
            }
            return self.insert_many_slots_assume_capacity(idx, count);
        }

        pub fn insert_many_slots_assume_capacity(self: *List, idx: Idx, count: Idx) []T {
            assert(idx <= self.len);
            mem.copyBackwards(T, self.ptr[idx + count .. self.len + count], self.ptr[idx..self.len]);
            return self.ptr[idx .. idx + count];
        }

        pub fn insert_slice(self: *List, idx: Idx, items: []const T) if (RETURN_ERRORS) Error!void else void {
            const slots = if (RETURN_ERRORS) try self.insert_many_slots(idx, @intCast(items.len)) else self.insert_slot(idx, @intCast(items.len));
            @memcpy(slots, items);
        }

        pub fn insert_slice_assume_capacity(self: *List, idx: usize, items: []const T) void {
            const slots = self.insert_many_slots_assume_capacity(idx, @intCast(items.len));
            @memcpy(slots, items);
        }

        pub fn replace_range(self: *List, start: Idx, length: Idx, new_items: []const T) if (RETURN_ERRORS) Error!void else void {
            if (new_items.len > length) {
                const additional_needed = new_items.len - length;
                if (RETURN_ERRORS) {
                    try self.ensure_unused_capacity(additional_needed);
                } else {
                    self.ensure_unused_capacity(additional_needed);
                }
            }
            self.replace_range_assume_capacity(start, length, new_items);
        }

        pub fn replace_range_assume_capacity(self: *List, start: Idx, length: Idx, new_items: []const T) void {
            const end_of_range = start + length;
            assert(end_of_range <= self.len);
            const range = self.ptr[start..end_of_range];
            if (range.len == new_items.len)
                @memcpy(range[0..new_items.len], new_items)
            else if (range.len < new_items.len) {
                const within_range = new_items[0..range.len];
                const leftover = new_items[range.len..];
                @memcpy(range[0..within_range.len], within_range);
                const new_slots = self.insert_many_slots_assume_capacity(end_of_range, leftover.len);
                @memcpy(new_slots, leftover);
            } else {
                const unused_slots = range.len - new_items.len;
                @memcpy(range[0..new_items.len], new_items);
                std.mem.copyForwards(T, self.ptr[end_of_range - unused_slots .. self.len], self.ptr[end_of_range..self.len]);
                if (SECURE_WIPE) {
                    crypto.secureZero(T, self.ptr[self.len - unused_slots .. self.len]);
                }
                self.len -= unused_slots;
            }
        }

        pub fn append(self: *List, item: T) if (RETURN_ERRORS) Error!void else void {
            const slot = if (RETURN_ERRORS) try self.append_slot() else self.append_slot();
            slot.* = item;
        }

        pub fn append_assume_capacity(self: *List, item: T) void {
            const slot = self.append_slot_assume_capacity();
            slot.* = item;
        }

        pub fn remove(self: *List, idx: Idx) T {
            const val: T = self.ptr[idx];
            self.delete(idx);
            return val;
        }

        pub fn swap_remove(self: *List, idx: Idx) T {
            const val: T = self.ptr[idx];
            self.swap_delete(idx);
            return val;
        }

        pub fn delete(self: *List, idx: Idx) void {
            assert(idx < self.len);
            std.mem.copyForwards(T, self.ptr[idx..self.len], self.ptr[idx + 1 .. self.len]);
            if (SECURE_WIPE) {
                crypto.secureZero(T, self.ptr[self.len - 1 .. self.len]);
            }
            self.len -= 1;
        }

        pub fn delete_range(self: *List, start: Idx, length: Idx) void {
            const end_of_range = start + length;
            assert(end_of_range <= self.len);
            std.mem.copyForwards(T, self.ptr[start..self.len], self.ptr[end_of_range..self.len]);
            if (SECURE_WIPE) {
                crypto.secureZero(T, self.ptr[self.len - length .. self.len]);
            }
            self.len -= length;
        }

        pub fn swap_delete(self: *List, idx: Idx) void {
            assert(idx < self.len);
            self.ptr[idx] = self.ptr[self.list.items.len - 1];
            if (SECURE_WIPE) {
                crypto.secureZero(T, self.ptr[self.len - 1 .. self.len]);
            }
            self.len -= 1;
        }

        pub fn append_slice(self: *List, items: []const T) if (RETURN_ERRORS) Error!void else void {
            const slots = if (RETURN_ERRORS) try self.append_many_slots(@intCast(items.len)) else self.append_many_slots(@intCast(items.len));
            @memcpy(slots, items);
        }

        pub fn append_slice_assume_capacity(self: *List, items: []const T) void {
            const slots = self.append_many_slots_assume_capacity(@intCast(items.len));
            @memcpy(slots, items);
        }

        pub fn append_slice_unaligned(self: *List, items: []align(1) const T) if (RETURN_ERRORS) Error!void else void {
            const slots = if (RETURN_ERRORS) try self.append_many_slots(@intCast(items.len)) else self.append_many_slots(@intCast(items.len));
            @memcpy(slots, items);
        }

        pub fn append_slice_unaligned_assume_capacity(self: *List, items: []align(1) const T) void {
            const slots = self.append_many_slots_assume_capacity(@intCast(items.len));
            @memcpy(slots, items);
        }

        pub const WriterHandle = struct {
            list: *List,
        };

        pub const Writer = if (T != u8)
            @compileError("The Writer interface is only defined for child type `u8` " ++
                "but the given type is " ++ @typeName(T))
        else
            std.io.Writer(WriterHandle, Allocator.Error, write);

        pub fn get_writer(self: *List) Writer {
            return Writer{ .context = .{ .list = self } };
        }

        fn write(handle: WriterHandle, bytes: []const u8) Allocator.Error!usize {
            try handle.list.append_slice(bytes);
            return bytes.len;
        }

        pub const WriterNoGrow = if (T != u8)
            @compileError("The Writer interface is only defined for child type `u8` " ++
                "but the given type is " ++ @typeName(T))
        else
            std.io.Writer(WriterHandle, Allocator.Error, write_no_grow);

        pub fn get_writer_no_grow(self: *List) WriterNoGrow {
            return WriterNoGrow{ .context = .{ .list = self } };
        }

        fn write_no_grow(handle: WriterHandle, bytes: []const u8) error{OutOfMemory}!usize {
            const available_capacity = handle.list.list.capacity - handle.list.list.items.len;
            if (bytes.len > available_capacity) return error.OutOfMemory;
            handle.list.append_slice_assume_capacity(bytes);
            return bytes.len;
        }

        pub fn append_n_times(self: *List, value: T, count: Idx) if (RETURN_ERRORS) Error!void else void {
            const slots = if (RETURN_ERRORS) try self.append_many_slots(count) else self.append_many_slots(count);
            @memset(slots, value);
        }

        pub fn append_n_times_assume_capacity(self: *List, value: T, count: Idx) void {
            const slots = self.append_many_slots_assume_capacity(count);
            @memset(slots, value);
        }

        pub fn resize(self: *List, new_len: Idx) if (RETURN_ERRORS) Error!void else void {
            if (RETURN_ERRORS) {
                try self.ensure_total_capacity(new_len);
            } else {
                self.ensure_total_capacity(new_len);
            }
            if (SECURE_WIPE and new_len < self.len) {
                crypto.secureZero(T, self.ptr[new_len..self.len]);
            }
            self.len = new_len;
        }

        pub fn shrink_and_free(self: *List, new_len: Idx) void {
            assert(new_len <= self.len);

            if (@sizeOf(T) == 0) {
                self.items.len = new_len;
                return;
            }

            if (SECURE_WIPE) {
                crypto.secureZero(T, self.ptr[new_len..self.len]);
            }

            const old_memory = self.ptr[0..self.cap];
            if (ALLOC.remap(old_memory, new_len)) |new_items| {
                self.ptr = new_items.ptr;
                self.len = new_items.len;
                self.cap = new_items.len;
                return;
            }

            const new_memory = ALLOC.alignedAlloc(T, ALIGN, new_len) catch |err| switch (err) {
                error.OutOfMemory => {
                    self.len = new_len;
                    return;
                },
            };

            @memcpy(new_memory, self.ptr[0..new_len]);
            ALLOC.free(old_memory);
            self.ptr = new_memory.ptr;
            self.len = new_memory.len;
            self.cap = new_memory.len;
        }

        pub fn shrink_retaining_capacity(self: *List, new_len: Idx) void {
            assert(new_len <= self.len);
            if (SECURE_WIPE) {
                crypto.secureZero(T, self.ptr[new_len..self.len]);
            }
            self.len = new_len;
        }

        pub fn clear_retaining_capacity(self: *List) void {
            if (SECURE_WIPE) {
                std.crypto.secureZero(T, self.ptr[0..self.len]);
            }
            self.len = 0;
        }

        pub fn clear_and_free(self: *List) void {
            if (SECURE_WIPE) {
                std.crypto.secureZero(T, self.ptr[0..self.len]);
            }
            ALLOC.free(self.ptr[0..self.cap]);
            self.ptr = UNINIT_PTR;
            self.len = 0;
            self.cap = 0;
        }

        pub fn ensure_total_capacity(self: *List, new_capacity: Idx) if (RETURN_ERRORS) Error!void else void {
            if (self.cap >= new_capacity) return;
            return self.ensure_total_capacity_exact(true_capacity_for_grow(self.cap, new_capacity));
        }

        pub fn ensure_total_capacity_exact(self: *List, new_capacity: Idx) if (RETURN_ERRORS) Error!void else void {
            if (@sizeOf(T) == 0) {
                self.cap = math.maxInt(Idx);
                return;
            }

            if (self.cap >= new_capacity) return;

            if (new_capacity < self.len) {
                if (SECURE_WIPE) crypto.secureZero(T, self.ptr[new_capacity..self.len]);
                self.len = new_capacity;
            }

            const old_memory = self.ptr[0..self.cap];
            if (ALLOC.remap(old_memory, new_capacity)) |new_memory| {
                self.ptr = new_memory.ptr;
                self.cap = new_memory.len;
            } else {
                const new_memory = try ALLOC.alignedAlloc(T, ALIGN, new_capacity);
                @memcpy(new_memory[0..self.len], self.ptr[0..self.len]);
                if (SECURE_WIPE) crypto.secureZero(T, self.ptr[0..self.len]);
                ALLOC.free(old_memory);
                self.ptr = new_memory.ptr;
                self.cap = new_memory.len;
            }
        }

        pub fn ensure_unused_capacity(self: *List, additional_count: Idx) if (RETURN_ERRORS) Error!void else void {
            const new_total_cap = if (RETURN_ERRORS) try add_or_error(self.len, additional_count) else add_or_error(self.len, additional_count);
            return self.ensure_total_capacity(new_total_cap);
        }

        pub fn expand_to_capacity(self: *List) void {
            self.len = self.cap;
        }

        pub fn append_slot(self: *List) if (RETURN_ERRORS) Error!*T else *T {
            const new_len = self.len + 1;
            if (RETURN_ERRORS) try self.ensure_total_capacity(new_len) else self.ensure_total_capacity(new_len);
            return self.append_slot_assume_capacity();
        }

        pub fn append_slot_assume_capacity(self: *List) *T {
            assert(self.len < self.cap);
            const idx = self.len;
            self.len += 1;
            return &self.ptr[idx];
        }

        pub fn append_many_slots(self: *List, count: usize) if (RETURN_ERRORS) Error![]T else []T {
            const new_len = self.len + count;
            if (RETURN_ERRORS) try self.ensure_total_capacity(new_len) else self.ensure_total_capacity(new_len);
            return self.append_many_slots_assume_capacity(count);
        }

        pub fn append_many_slots_assume_capacity(self: *List, count: usize) []T {
            const new_len = self.len + count;
            assert(new_len <= self.cap);
            const prev_len = self.len;
            self.len = new_len;
            return self.ptr[prev_len..][0..count];
        }

        pub fn append_many_slots_as_array(self: *List, comptime count: usize) if (RETURN_ERRORS) Error!*[count]T else *[count]T {
            const new_len = self.len + count;
            if (RETURN_ERRORS) try self.ensure_total_capacity(new_len) else self.ensure_total_capacity(new_len);
            return self.append_many_slots_as_array_assume_capacity(count);
        }

        pub fn append_many_slots_as_array_assume_capacity(self: *List, comptime count: usize) *[count]T {
            const new_len = self.len + count;
            assert(new_len <= self.cap);
            const prev_len = self.len;
            self.len = new_len;
            return self.ptr[prev_len..][0..count];
        }

        pub fn pop_or_null(self: *List) ?T {
            if (self.len == 0) return null;
            return self.pop();
        }

        pub fn pop(self: *List) T {
            assert(self.len > 0);
            const new_len = self.len - 1;
            self.len = new_len;
            return self.ptr[new_len];
        }

        pub fn get_last(self: List) T {
            assert(self.len > 0);
            return self.ptr[self.len - 1];
        }

        pub inline fn get_last_or_null(self: List) ?T {
            if (self.len == 0) return null;
            return self.get_last();
        }

        fn add_or_error(a: Idx, b: Idx) if (RETURN_ERRORS) error{OutOfMemory}!Idx else Idx {
            if (!RETURN_ERRORS) return a + b;
            const result, const overflow = @addWithOverflow(a, b);
            if (overflow != 0) return error.OutOfMemory;
            return result;
        }

        const ATOMIC_PADDING = @as(comptime_int, @max(1, std.atomic.cache_line / @sizeOf(T)));

        fn true_capacity_for_grow(current: Idx, minimum: Idx) usize {
            switch (GROWTH) {
                GrowthModel.GROW_EXACT_NEEDED => {
                    return minimum;
                },
                GrowthModel.GROW_EXACT_NEEDED_WITH_ATOMIC_PADDING => {
                    return minimum + ATOMIC_PADDING;
                },
                else => {
                    var new = current;
                    while (true) {
                        switch (GROWTH) {
                            GrowthModel.GROW_BY_100_PERCENT => {
                                new +|= new;
                                if (new >= minimum) return new;
                            },
                            GrowthModel.GROW_BY_100_PERCENT_WITH_ATOMIC_PADDING => {
                                new +|= new;
                                const new_with_padding = new + ATOMIC_PADDING;
                                if (new_with_padding >= minimum) return new_with_padding;
                            },
                            GrowthModel.GROW_BY_50_PERCENT => {
                                new +|= new / 2;
                                if (new >= minimum) return new;
                            },
                            GrowthModel.GROW_BY_50_PERCENT_WITH_ATOMIC_PADDING => {
                                new +|= new / 2;
                                const new_with_padding = new + ATOMIC_PADDING;
                                if (new_with_padding >= minimum) return new_with_padding;
                            },
                            GrowthModel.GROW_BY_25_PERCENT => {
                                new +|= new / 4;
                                if (new >= minimum) return new;
                            },
                            GrowthModel.GROW_BY_25_PERCENT_WITH_ATOMIC_PADDING => {
                                new +|= new / 4;
                                const new_with_padding = new + ATOMIC_PADDING;
                                if (new_with_padding >= minimum) return new_with_padding;
                            },
                            else => unreachable,
                        }
                    }
                },
            }
        }

        fn handle_alloc_error(err: Allocator.Error) if (RETURN_ERRORS) Error else noreturn {
            switch (ALLOC_ERROR_BEHAVIOR) {
                AllocErrorBehavior.ALLOCATION_ERRORS_RETURN_ERROR => return err,
                AllocErrorBehavior.ALLOCATION_ERRORS_PANIC => std.debug.panic("[ErgoList] List's backing allocator failed to allocate memory: Allocator.Error.{s}", .{@errorName(err)}),
                AllocErrorBehavior.ALLOCATION_ERRORS_ARE_UNREACHABLE => unreachable,
            }
        }
    };
}
