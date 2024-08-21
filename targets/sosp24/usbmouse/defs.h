#include <linux/kernel.h>
#include <linux/slab.h>
#include <linux/module.h>
#include <linux/init.h>
#include <linux/usb/input.h>
#include <linux/hid.h>

#include "stdbool.h"

struct usb_interface; // can't compile without this.

struct usb_mouse {
	char name[128];
	char phys[64];
	struct usb_device *usbdev;
	struct input_dev *dev;
	struct urb *irq;

	signed char *data;
	dma_addr_t data_dma;
};

// -------------------------------//

// Verifast models submitted urbs as resources using the urb_submitted predicate
// We instead use a simple model that keeps a history of submitted urbs.

enum urb_status {
	NONE, 		// The URB has not been submitted.
	SENT,		// We know the USB core received it. We don't own the URB anymore
	RCV_BACK,	// The core processed the request and called the callback.
	DONE		// The callback is done with the request. We own the URB.
};
struct urb_hist_rec {
    struct urb req;
	enum urb_status status;
    // struct urb_hist_rec *next;
};


extern struct urb_hist_rec urb_rec;
extern struct input_dev *reportable_dev;
extern struct input_dev *registered_dev;

struct urb_hist_rec* model__urb_get_record(struct urb *urb);
