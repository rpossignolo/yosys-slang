/*
 * Interface-to-Port Conversion Header for Yosys-Slang
 */

#pragma once

#include "slang_frontend.h"

namespace yosys_slang {
    
    // Convert interface ports to regular I/O ports for synthesis
    void convertInterfacePortsToIO(slang_frontend::NetlistContext& netlist, const slang::ast::InstanceBodySymbol& body);
    
} // namespace yosys_slang