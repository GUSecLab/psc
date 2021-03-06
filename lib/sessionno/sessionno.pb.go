// Code generated by protoc-gen-go. DO NOT EDIT.
// source: sessionno.proto

package Sessionno

import (
	fmt "fmt"
	proto "github.com/golang/protobuf/proto"
	math "math"
)

// Reference imports to suppress errors if they are not otherwise used.
var _ = proto.Marshal
var _ = fmt.Errorf
var _ = math.Inf

// This is a compile-time assertion to ensure that this generated file
// is compatible with the proto package it is being compiled against.
// A compilation error at this line likely means your copy of the
// proto package needs to be updated.
const _ = proto.ProtoPackageIsVersion3 // please upgrade the proto package

type SNo struct {
	S                    *uint32  `protobuf:"varint,1,req,name=S,json=s" json:"S,omitempty"`
	XXX_NoUnkeyedLiteral struct{} `json:"-"`
	XXX_unrecognized     []byte   `json:"-"`
	XXX_sizecache        int32    `json:"-"`
}

func (m *SNo) Reset()         { *m = SNo{} }
func (m *SNo) String() string { return proto.CompactTextString(m) }
func (*SNo) ProtoMessage()    {}
func (*SNo) Descriptor() ([]byte, []int) {
	return fileDescriptor_f464bbea306f7d66, []int{0}
}

func (m *SNo) XXX_Unmarshal(b []byte) error {
	return xxx_messageInfo_SNo.Unmarshal(m, b)
}
func (m *SNo) XXX_Marshal(b []byte, deterministic bool) ([]byte, error) {
	return xxx_messageInfo_SNo.Marshal(b, m, deterministic)
}
func (m *SNo) XXX_Merge(src proto.Message) {
	xxx_messageInfo_SNo.Merge(m, src)
}
func (m *SNo) XXX_Size() int {
	return xxx_messageInfo_SNo.Size(m)
}
func (m *SNo) XXX_DiscardUnknown() {
	xxx_messageInfo_SNo.DiscardUnknown(m)
}

var xxx_messageInfo_SNo proto.InternalMessageInfo

func (m *SNo) GetS() uint32 {
	if m != nil && m.S != nil {
		return *m.S
	}
	return 0
}

func init() {
	proto.RegisterType((*SNo)(nil), "Sessionno.SNo")
}

func init() { proto.RegisterFile("sessionno.proto", fileDescriptor_f464bbea306f7d66) }

var fileDescriptor_f464bbea306f7d66 = []byte{
	// 67 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0xe2, 0xe2, 0x2f, 0x4e, 0x2d, 0x2e,
	0xce, 0xcc, 0xcf, 0xcb, 0xcb, 0xd7, 0x2b, 0x28, 0xca, 0x2f, 0xc9, 0x17, 0xe2, 0x0c, 0x86, 0x09,
	0x28, 0x09, 0x73, 0x31, 0x07, 0xfb, 0xe5, 0x0b, 0xf1, 0x70, 0x31, 0x06, 0x4b, 0x30, 0x2a, 0x30,
	0x69, 0xf0, 0x06, 0x31, 0x16, 0x03, 0x02, 0x00, 0x00, 0xff, 0xff, 0x5c, 0x4e, 0xb3, 0xd1, 0x31,
	0x00, 0x00, 0x00,
}
