#include "SmokerWrapper.h"
#include "EverParse.h"
#include "Smoker.h"
void SmokerEverParseError(const char *StructName, const char *FieldName, const char *Reason);

static
void DefaultErrorHandler(
	const char *typename,
	const char *fieldname,
	const char *reason,
	uint8_t *context,
	EverParseInputBuffer input,
	uint32_t start_pos)
{
	EverParseErrorFrame *frame = (EverParseErrorFrame*)context;
	EverParseDefaultErrorHandler(
		typename,
		fieldname,
		reason,
		frame,
		input,
		start_pos
	);
}

BOOLEAN SmokerCheckSmoker(uint8_t *base, uint32_t len) {
	EverParseErrorFrame frame;
	frame.filled = FALSE;
	EverParseInputBuffer input = EverParseMakeInputBuffer(base, len);
	uint64_t result = SmokerValidateSmoker( (uint8_t*)&frame, &DefaultErrorHandler, input, 0);
	if (EverParseResultIsError(result))
	{
		if (frame.filled)
		{
			SmokerEverParseError(frame.typename, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}
