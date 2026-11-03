#!/usr/bin/env bash
# Copyright Kani Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT

# The bodies that autoharness generates must start the aliasing monitor and pass tags to the
# function under verification. Without that, CBMC aborted on the first store of a pointer
# ("kani_alias_tag_inv should exist").
rm -rf target
cargo kani autoharness -Z autoharness -Z aliasing-checks -j 1
