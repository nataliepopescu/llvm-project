"""
Test completing types using information from other shared libraries.
"""

import os
import lldb
from lldbsuite.test.decorators import *
from lldbsuite.test.lldbtest import *
from lldbsuite.test import lldbutil


class LimitDebugInfoTestCase(TestBase):

    mydir = TestBase.compute_mydir(__file__)

    def _check_type(self, target, name):
        exe = target.FindModule(lldb.SBFileSpec("a.out"))
        type_ = exe.FindFirstType(name)
        self.trace("type_: %s"%type_)
        self.assertTrue(type_)
        base = type_.GetDirectBaseClassAtIndex(0).GetType()
        self.trace("base:%s"%base)
        self.assertTrue(base)
        self.assertEquals(base.GetNumberOfFields(), 0)

    def _check_debug_info_is_limited(self, target):
        # Without other shared libraries we should only see the member declared
        # in the derived class. This serves as a sanity check that we are truly
        # building with limited debug info.
        self._check_type(target, "InheritsFromOne")
        self._check_type(target, "InheritsFromTwo")

    @skipIf(bugnumber="pr46284", debug_info="gmodules")
    @skipIfWindows # Clang emits type info even with -flimit-debug-info
    def test_one_and_two_debug(self):
        self.build()
        target = self.dbg.CreateTarget(self.getBuildArtifact("a.out"))

        self._check_debug_info_is_limited(target)

        self.registerSharedLibrariesWithTarget(target, ["one", "two"])

        # But when other shared libraries are loaded, we should be able to see
        # all members.
        self.expect_expr("inherits_from_one.member", result_value="47")
        self.expect_expr("inherits_from_one.one", result_value="142")
        self.expect_expr("inherits_from_two.member", result_value="47")
        self.expect_expr("inherits_from_two.one", result_value="142")
        self.expect_expr("inherits_from_two.two", result_value="242")

        self.expect_expr("one_as_member.member", result_value="47")
        self.expect_expr("one_as_member.one.member", result_value="147")
        self.expect_expr("two_as_member.member", result_value="47")
        self.expect_expr("two_as_member.two.one.member", result_value="147")
        self.expect_expr("two_as_member.two.member", result_value="247")

    @skipIf(bugnumber="pr46284", debug_info="gmodules")
    @skipIfWindows # Clang emits type info even with -flimit-debug-info
    def test_two_debug(self):
        self.build(dictionary=dict(STRIP_ONE="1"))
        target = self.dbg.CreateTarget(self.getBuildArtifact("a.out"))

        self._check_debug_info_is_limited(target)

        self.registerSharedLibrariesWithTarget(target, ["one", "two"])

        # This time, we should only see the members from the second library.
        self.expect_expr("inherits_from_one.member", result_value="47")
        self.expect("expr inherits_from_one.one", error=True,
            substrs=["no member named 'one' in 'InheritsFromOne'"])
        self.expect_expr("inherits_from_two.member", result_value="47")
        self.expect("expr inherits_from_two.one", error=True,
            substrs=["no member named 'one' in 'InheritsFromTwo'"])
        self.expect_expr("inherits_from_two.two", result_value="242")

        self.expect_expr("one_as_member.member", result_value="47")
        self.expect("expr one_as_member.one.member", error=True,
                substrs=["no member named 'member' in 'member::One'"])
        self.expect_expr("two_as_member.member", result_value="47")
        self.expect("expr two_as_member.two.one.member", error=True,
                substrs=["no member named 'member' in 'member::One'"])
        self.expect_expr("two_as_member.two.member", result_value="247")

    @skipIf(bugnumber="pr46284", debug_info="gmodules")
    @skipIfWindows # Clang emits type info even with -flimit-debug-info
    def test_one_debug(self):
        self.build(dictionary=dict(STRIP_TWO="1"))
        target = self.dbg.CreateTarget(self.getBuildArtifact("a.out"))

        self._check_debug_info_is_limited(target)

        self.registerSharedLibrariesWithTarget(target, ["one", "two"])

        # In this case we should only see the members from the second library.
        # Note that we cannot see inherits_from_two.one because without debug
        # info for "Two", we cannot determine that it in fact inherits from
        # "One".
        self.expect_expr("inherits_from_one.member", result_value="47")
        self.expect_expr("inherits_from_one.one", result_value="142")
        self.expect_expr("inherits_from_two.member", result_value="47")
        self.expect("expr inherits_from_two.one", error=True,
            substrs=["no member named 'one' in 'InheritsFromTwo'"])
        self.expect("expr inherits_from_two.two", error=True,
            substrs=["no member named 'two' in 'InheritsFromTwo'"])

        self.expect_expr("one_as_member.member", result_value="47")
        self.expect_expr("one_as_member.one.member", result_value="147")
        self.expect_expr("two_as_member.member", result_value="47")
        self.expect("expr two_as_member.two.one.member", error=True,
                substrs=["no member named 'one' in 'member::Two'"])
        self.expect("expr two_as_member.two.member", error=True,
                substrs=["no member named 'member' in 'member::Two'"])
