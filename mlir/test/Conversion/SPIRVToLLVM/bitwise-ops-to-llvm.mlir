// RUN: mlir-opt -convert-spirv-to-llvm %s | FileCheck %s

//===----------------------------------------------------------------------===//
// spv.BitCount
//===----------------------------------------------------------------------===//

func @bitcount_scalar(%arg0: i16) {
	// CHECK: %{{.*}} = "llvm.intr.ctpop"(%{{.*}}) : (!llvm.i16) -> !llvm.i16
	%0 = spv.BitCount %arg0: i16
	return
}

func @bitcount_vector(%arg0: vector<3xi32>) {
	// CHECK: %{{.*}} = "llvm.intr.ctpop"(%{{.*}}) : (!llvm<"<3 x i32>">) -> !llvm<"<3 x i32>">
	%0 = spv.BitCount %arg0: vector<3xi32>
	return
}

//===----------------------------------------------------------------------===//
// spv.BitReverse
//===----------------------------------------------------------------------===//

func @bitreverse_scalar(%arg0: i64) {
	// CHECK: %{{.*}} = "llvm.intr.bitreverse"(%{{.*}}) : (!llvm.i64) -> !llvm.i64
	%0 = spv.BitReverse %arg0: i64
	return
}

func @bitreverse_vector(%arg0: vector<4xi32>) {
	// CHECK: %{{.*}} = "llvm.intr.bitreverse"(%{{.*}}) : (!llvm<"<4 x i32>">) -> !llvm<"<4 x i32>">
	%0 = spv.BitReverse %arg0: vector<4xi32>
	return
}

//===----------------------------------------------------------------------===//
// spv.BitFieldInsert
//===----------------------------------------------------------------------===//

// CHECK-LABEL: func @bitfield_insert_scalar_same_bit_width
// CHECK-SAME: %[[BASE:.*]]: !llvm.i32, %[[INSERT:.*]]: !llvm.i32, %[[OFFSET:.*]]: !llvm.i32, %[[COUNT:.*]]: !llvm.i32
func @bitfield_insert_scalar_same_bit_width(%base: i32, %insert: i32, %offset: i32, %count: i32) {
    // CHECK: %[[MINUS_ONE:.*]] = llvm.mlir.constant(-1 : i32) : !llvm.i32
    // CHECK: %[[T0:.*]] = llvm.shl %[[MINUS_ONE]], %[[COUNT]] : !llvm.i32
    // CHECK: %[[T1:.*]] = llvm.xor %[[T0]], %[[MINUS_ONE]] : !llvm.i32
    // CHECK: %[[T2:.*]] = llvm.shl %[[T1]], %[[OFFSET]] : !llvm.i32
    // CHECK: %[[MASK:.*]] = llvm.xor %[[T2]], %[[MINUS_ONE]] : !llvm.i32
    // CHECK: %[[NEW_BASE:.*]] = llvm.and %[[BASE]], %[[MASK]] : !llvm.i32
    // CHECK: %[[SHIFTED_INSERT:.*]] = llvm.shl %[[INSERT]], %[[OFFSET]] : !llvm.i32
    // CHECK: %{{.*}} = llvm.or %[[NEW_BASE]], %[[SHIFTED_INSERT]] : !llvm.i32
    %0 = spv.BitFieldInsert %base, %insert, %offset, %count : i32, i32, i32
    return
}

// CHECK-LABEL: func @bitfield_insert_scalar_smaller_bit_width
// CHECK-SAME: %[[BASE:.*]]: !llvm.i64, %[[INSERT:.*]]: !llvm.i64, %[[OFFSET:.*]]: !llvm.i8, %[[COUNT:.*]]: !llvm.i8
func @bitfield_insert_scalar_smaller_bit_width(%base: i64, %insert: i64, %offset: i8, %count: i8) {
    // CHECK: %[[MINUS_ONE:.*]] = llvm.mlir.constant(-1 : i64) : !llvm.i64
    // CHECK: %[[EXT_COUNT:.*]] = llvm.zext %[[COUNT]] : !llvm.i8 to !llvm.i64
    // CHECK: %[[EXT_OFFSET:.*]] = llvm.zext %[[OFFSET]] : !llvm.i8 to !llvm.i64
    // CHECK: %[[T0:.*]] = llvm.shl %[[MINUS_ONE]], %[[EXT_COUNT]] : !llvm.i64
    // CHECK: %[[T1:.*]] = llvm.xor %[[T0]], %[[MINUS_ONE]] : !llvm.i64
    // CHECK: %[[T2:.*]] = llvm.shl %[[T1]], %[[EXT_OFFSET]] : !llvm.i64
    // CHECK: %[[MASK:.*]] = llvm.xor %[[T2]], %[[MINUS_ONE]] : !llvm.i64
    // CHECK: %[[NEW_BASE:.*]] = llvm.and %[[BASE]], %[[MASK]] : !llvm.i64
    // CHECK: %[[SHIFTED_INSERT:.*]] = llvm.shl %[[INSERT]], %[[EXT_OFFSET]] : !llvm.i64
    // CHECK: %{{.*}} = llvm.or %[[NEW_BASE]], %[[SHIFTED_INSERT]] : !llvm.i64
    %0 = spv.BitFieldInsert %base, %insert, %offset, %count : i64, i8, i8
    return
}

// CHECK-LABEL: func @bitfield_insert_scalar_greater_bit_width
// CHECK-SAME: %[[BASE:.*]]: !llvm.i16, %[[INSERT:.*]]: !llvm.i16, %[[OFFSET:.*]]: !llvm.i32, %[[COUNT:.*]]: !llvm.i64
func @bitfield_insert_scalar_greater_bit_width(%base: i16, %insert: i16, %offset: i32, %count: i64) {
    // CHECK: %[[MINUS_ONE:.*]] = llvm.mlir.constant(-1 : i16) : !llvm.i16
    // CHECK: %[[TRUNC_COUNT:.*]] = llvm.trunc %[[COUNT]] : !llvm.i64 to !llvm.i16
    // CHECK: %[[TRUNC_OFFSET:.*]] = llvm.trunc %[[OFFSET]] : !llvm.i32 to !llvm.i16
    // CHECK: %[[T0:.*]] = llvm.shl %[[MINUS_ONE]], %[[TRUNC_COUNT]] : !llvm.i16
    // CHECK: %[[T1:.*]] = llvm.xor %[[T0]], %[[MINUS_ONE]] : !llvm.i16
    // CHECK: %[[T2:.*]] = llvm.shl %[[T1]], %[[TRUNC_OFFSET]] : !llvm.i16
    // CHECK: %[[MASK:.*]] = llvm.xor %[[T2]], %[[MINUS_ONE]] : !llvm.i16
    // CHECK: %[[NEW_BASE:.*]] = llvm.and %[[BASE]], %[[MASK]] : !llvm.i16
    // CHECK: %[[SHIFTED_INSERT:.*]] = llvm.shl %[[INSERT]], %[[TRUNC_OFFSET]] : !llvm.i16
    // CHECK: %{{.*}} = llvm.or %[[NEW_BASE]], %[[SHIFTED_INSERT]] : !llvm.i16
    %0 = spv.BitFieldInsert %base, %insert, %offset, %count : i16, i32, i64
    return
}

// CHECK-LABEL: func @bitfield_insert_vector
// CHECK-SAME: %[[BASE:.*]]: !llvm<"<2 x i32>">, %[[INSERT:.*]]: !llvm<"<2 x i32>">, %[[OFFSET:.*]]: !llvm.i32, %[[COUNT:.*]]: !llvm.i32
func @bitfield_insert_vector(%base: vector<2xi32>, %insert: vector<2xi32>, %offset: i32, %count: i32) {
    // CHECK: %[[OFFSET_V0:.*]] = llvm.mlir.undef : !llvm<"<2 x i32>">
    // CHECK: %[[ZERO:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
    // CHECK: %[[OFFSET_V1:.*]] = llvm.insertelement %[[OFFSET]], %[[OFFSET_V0]][%[[ZERO]] : !llvm.i32] : !llvm<"<2 x i32>">
    // CHECK: %[[ONE:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
    // CHECK: %[[OFFSET_V2:.*]] = llvm.insertelement  %[[OFFSET]], %[[OFFSET_V1]][%[[ONE]] : !llvm.i32] : !llvm<"<2 x i32>">
    // CHECK: %[[COUNT_V0:.*]] = llvm.mlir.undef : !llvm<"<2 x i32>">
    // CHECK: %[[ZERO:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
    // CHECK: %[[COUNT_V1:.*]] = llvm.insertelement %[[COUNT]], %[[COUNT_V0]][%[[ZERO]] : !llvm.i32] : !llvm<"<2 x i32>">
    // CHECK: %[[ONE:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
    // CHECK: %[[COUNT_V2:.*]] = llvm.insertelement %[[COUNT]], %[[COUNT_V1]][%[[ONE]] : !llvm.i32] : !llvm<"<2 x i32>">
    // CHECK: %[[MINUS_ONE:.*]] = llvm.mlir.constant(dense<-1> : vector<2xi32>) : !llvm<"<2 x i32>">
    // CHECK: %[[T0:.*]] = llvm.shl %[[MINUS_ONE]], %[[COUNT_V2]] : !llvm<"<2 x i32>">
    // CHECK: %[[T1:.*]] = llvm.xor %[[T0]], %[[MINUS_ONE]] : !llvm<"<2 x i32>">
    // CHECK: %[[T2:.*]] = llvm.shl %[[T1]], %[[OFFSET_V2]] : !llvm<"<2 x i32>">
    // CHECK: %[[MASK:.*]] = llvm.xor %[[T2]], %[[MINUS_ONE]] : !llvm<"<2 x i32>">
    // CHECK: %[[NEW_BASE:.*]] = llvm.and %[[BASE]], %[[MASK]] : !llvm<"<2 x i32>">
    // CHECK: %[[SHIFTED_INSERT:.*]] = llvm.shl %[[INSERT]], %[[OFFSET_V2]] : !llvm<"<2 x i32>">
    // CHECK: %{{.*}} = llvm.or %[[NEW_BASE]], %[[SHIFTED_INSERT]] : !llvm<"<2 x i32>">
    %0 = spv.BitFieldInsert %base, %insert, %offset, %count : vector<2xi32>, i32, i32
    return
}

//===----------------------------------------------------------------------===//
// spv.BitwiseAnd
//===----------------------------------------------------------------------===//

func @bitwise_and_scalar(%arg0: i32, %arg1: i32) {
	// CHECK: %{{.*}} = llvm.and %{{.*}}, %{{.*}} : !llvm.i32
	%0 = spv.BitwiseAnd %arg0, %arg1 : i32
	return
}

func @bitwise_and_vector(%arg0: vector<4xi64>, %arg1: vector<4xi64>) {
	// CHECK: %{{.*}} = llvm.and %{{.*}}, %{{.*}} : !llvm<"<4 x i64>">
	%0 = spv.BitwiseAnd %arg0, %arg1 : vector<4xi64>
	return
}

//===----------------------------------------------------------------------===//
// spv.BitwiseOr
//===----------------------------------------------------------------------===//

func @bitwise_or_scalar(%arg0: i64, %arg1: i64) {
	// CHECK: %{{.*}} = llvm.or %{{.*}}, %{{.*}} : !llvm.i64
	%0 = spv.BitwiseOr %arg0, %arg1 : i64
	return
}

func @bitwise_or_vector(%arg0: vector<3xi8>, %arg1: vector<3xi8>) {
	// CHECK: %{{.*}} = llvm.or %{{.*}}, %{{.*}} : !llvm<"<3 x i8>">
	%0 = spv.BitwiseOr %arg0, %arg1 : vector<3xi8>
	return
}

//===----------------------------------------------------------------------===//
// spv.BitwiseXor
//===----------------------------------------------------------------------===//

func @bitwise_xor_scalar(%arg0: i32, %arg1: i32) {
	// CHECK: %{{.*}} = llvm.xor %{{.*}}, %{{.*}} : !llvm.i32
	%0 = spv.BitwiseXor %arg0, %arg1 : i32
	return
}

func @bitwise_xor_vector(%arg0: vector<2xi16>, %arg1: vector<2xi16>) {
	// CHECK: %{{.*}} = llvm.xor %{{.*}}, %{{.*}} : !llvm<"<2 x i16>">
	%0 = spv.BitwiseXor %arg0, %arg1 : vector<2xi16>
	return
}

//===----------------------------------------------------------------------===//
// spv.Not
//===----------------------------------------------------------------------===//

func @not__scalar(%arg0: i32) {
  // CHECK: %[[CONST:.*]] = llvm.mlir.constant(-1 : i32) : !llvm.i32
  // CHECK: %{{.*}} = llvm.xor %{{.*}}, %[[CONST]] : !llvm.i32
	%0 = spv.Not %arg0 : i32
  return
}

func @not_vector(%arg0: vector<2xi16>) {
  // CHECK: %[[CONST:.*]] = llvm.mlir.constant(dense<-1> : vector<2xi16>) : !llvm<"<2 x i16>">
  // CHECK: %{{.*}} = llvm.xor %{{.*}}, %[[CONST]] : !llvm<"<2 x i16>">
	%0 = spv.Not %arg0 : vector<2xi16>
  return
}
