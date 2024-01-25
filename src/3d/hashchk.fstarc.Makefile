# This file is intended to be used with $(MAKE) -C $(FSTAR_HOME)/src
include Makefile.boot

# And then, in a separate invocation, from each .checked.lax we
# extract an .ml file
$(ALL_FS_FILES): %.fs:
	$(call msg, "EXTRACT", $(notdir $@))
	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $(notdir $(subst .checked.lax,,$<)) \
		   --odir "$(call OUTPUT_DIRECTORY_FOR,"$@")" \
		   --codegen FSharp \
		   --extract_module $(basename $(notdir $(subst .checked.lax,,$<)))

$(EVERPARSE_HASHCHK_OUTPUT_DIRECTORY)/%.fs: $(OUTPUT_DIRECTORY)/%.fs
	cp $< $@
