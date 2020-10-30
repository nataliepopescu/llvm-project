add_llvm_library( LLVMBoundsCheckOpti MODULE
  BoundsCheckOpti.cpp
	
	DEPENDS
	intrinsics_gen
  PLUGIN_TOOL
  opt
  )
