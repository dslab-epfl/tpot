#include "defs.h"
#include <tpot_primitives.h>

// --------------- //
// --- helpers --- //
// --------------- //
struct urb_hist_rec urb_rec;
struct input_dev *reportable_dev;
struct input_dev *registered_dev;

void model__add_urb_record(struct urb *urb, enum urb_status status) {

    struct urb_hist_rec *n = &urb_rec;
    struct urb *req = &n->req;
    req->dev = urb->dev;
    req->status = urb->status;
    req->transfer_flags = urb->transfer_flags;
    req->transfer_dma = urb->transfer_dma;
    req->setup_packet = urb->setup_packet;
    req->context = urb->context;

    n->status = status;
} /*SYNTAX*/ 

struct urb_hist_rec* model__urb_get_record(struct urb *urb) {
    struct urb_hist_rec *rec = &urb_rec;
    struct urb *last = &rec->req;
    if (last->dev == urb->dev
        && last->status == urb->status
        && last->transfer_flags == urb->transfer_flags
        && last->transfer_dma == urb->transfer_dma
        && last->setup_packet == urb->setup_packet
        && last->context == urb->context)
        return rec;

    return NULL; /*SYNTAX*/
} /*SYNTAX*/ 

// --------------- //
// --- Models ---- //
// --------------- //

// -- models that are pretty much the linux implementation -- //
void *input_get_drvdata(struct input_dev *dev) {
    // CC: We could also just put the linux implementaiton here. It's the same.
    return dev->dev.driver_data;
} /*SYNTAX*/ 
void input_set_drvdata(struct input_dev *dev, void *data) {
    dev->dev.driver_data = data;
} /*SYNTAX*/ 
void usb_set_intfdata(struct usb_interface *intf, void *data) {
    // Taken from the acutal linux definition.
    intf->dev.driver_data = data;
} /*SYNTAX*/ 
void *usb_get_intfdata(struct usb_interface *intf) {
    // Taken from the acutal linux definition.
    return intf->dev.driver_data;
} /*SYNTAX*/ 
int usb_pipeout(int pipe) {
    // Taken from the acutal linux definition.
    return !((pipe) & USB_DIR_IN);
} /*SYNTAX*/ 
#define USB_ENDPOINT_XFERTYPE_MASK	0x03	/* in bmAttributes */
#define USB_ENDPOINT_XFER_INT		3
#define USB_ENDPOINT_DIR_MASK		0x80
#define USB_DIR_IN			        0x80	/* to host */
int usb_endpoint_is_int_in(const struct usb_endpoint_descriptor *epd) {
    // Taken from the acutal linux definition.
    return ((epd->bmAttributes & USB_ENDPOINT_XFERTYPE_MASK) == USB_ENDPOINT_XFER_INT) &&
           ((epd->bEndpointAddress & USB_ENDPOINT_DIR_MASK) == USB_DIR_IN);
} /*SYNTAX*/ 
struct usb_device *interface_to_usbdev(struct usb_interface *intf) {
    // Taken from the acutal linux definition.
    return (struct usb_device *) intf->dev.parent;
} /*SYNTAX*/ 
void usb_fill_int_urb(struct urb *urb,
	struct usb_device *dev,
	/*unsigned*/ int pipe,
	void *transfer_buffer,
	int buffer_length,
	usb_complete_t complete_fn,
	void *context,
	int interval) {
    // Taken from the acutal linux definition.

    urb->dev = dev;
	// urb->pipe = pipe;
	// urb->transfer_buffer = transfer_buffer;
	// urb->transfer_buffer_length = buffer_length;
	// urb->complete = complete_fn;
	urb->context = context;

	// if (dev->speed == USB_SPEED_HIGH || dev->speed >= USB_SPEED_SUPER) {
	// 	/* make sure interval is within allowed range */
	// 	interval = clamp(interval, 1, 16);

	// 	urb->interval = 1 << (interval - 1);
	// } else {
	// 	urb->interval = interval;
	// }

	// urb->start_frame = -1;
} /*SYNTAX*/ 
void
usb_to_input_id(const struct usb_device *dev, struct input_id *id) {
    // This safely relaxes the linux implementation by havocing.
    any(__u16, bustype);
    any(__u16, vendor);
    any(__u16, product);
    any(__u16, version);
    id->bustype = bustype;
    id->vendor = vendor;
    id->product = product;
    id->version = version;
} /*SYNTAX*/ 

// -- memory management-related models -- //
void *kzalloc(size_t size, gfp_t flags) {
    // we don't care about zero initialization.
    any(int, success);
    if (!(success == 0)) {
        return NULL; /*SYNTAX*/
    } /*SYNTAX*/ 
    return tpot_malloc(size);
} /*SYNTAX*/ 
struct input_dev *input_allocate_device(void) {
    any(int, success);
    if (!(success == 0)) {
        return NULL; /*SYNTAX*/
    } /*SYNTAX*/ 
    struct input_dev *dev = tpot_malloc(sizeof(struct input_dev));
    reportable_dev = dev;
    return dev;
} /*SYNTAX*/ 
void input_free_device(struct input_dev *dev) {
    if (dev) {
        tpot_free(dev);
        reportable_dev = NULL;
    } /*SYNTAX*/ 
} /*SYNTAX*/ 
void kfree(void *ptr) {
    if (ptr)
        tpot_free(ptr);
} /*SYNTAX*/ 
struct urb *usb_alloc_urb(int iso_packets, gfp_t mem_flags) {
    assert(iso_packets == 0);
    any(int, success);
    if (!(success == 0)) 
        return NULL; /*SYNTAX*/

    return tpot_malloc(sizeof(struct urb));
} /*SYNTAX*/ 
void usb_free_coherent(struct usb_device *dev, size_t size, void *addr, dma_addr_t dma) {
    if (addr) 
        tpot_free(addr);
} /*SYNTAX*/ 
void usb_free_urb(struct urb *urb) {
    if (urb)
        tpot_free(urb);
} /*SYNTAX*/ 

void *usb_alloc_coherent(struct usb_device *dev, size_t size, gfp_t mem_flags, dma_addr_t* dma) {
    assert(size >= 0);
    // this needs to be accessible
    any(int, success);
    if (!(success == 0)) {
        return NULL; /*SYNTAX*/
    } else {
        any(dma_addr_t, dma_out);
        *dma = dma_out;
        return tpot_malloc(size);
    } /*SYNTAX*/ 
} /*SYNTAX*/ 

// -- string manipulation -- //
size_t strlcat(char* dest, const char * src, size_t count) {
    assert(count > 0);
    // dummy implementation that refines the verifast spec.
    dest[0] = '\0';
    return 0;
} /*SYNTAX*/ 
size_t strlen(const char *s) {
    // safely overestimate: can return anything
    any(size_t, len);
    return len;
} /*SYNTAX*/ 
size_t strlcpy(char * dest, const char * src, size_t size) {
    /*nop*/
} /*SYNTAX*/ 
int usb_make_path(struct usb_device *dev, char *buf, size_t size) {
    // dummy implementation that refines the verifast spec.
    buf[0] = '\0';
    return 0;
} /*SYNTAX*/ 

// -- Interact with the input subsystem -- //
void input_report_key(struct input_dev *dev, /*unsigned*/ int code, int value) {
    assert(reportable_dev == dev);
} /*SYNTAX*/ 
void input_report_rel(struct input_dev *dev, unsigned int code, int value) {
    assert(reportable_dev == dev);
} /*SYNTAX*/ 
void input_sync(struct input_dev *dev) {
    assert(reportable_dev == dev);
} /*SYNTAX*/ 

// -- URB transmission -- //
int usb_submit_urb(struct urb *urb, gfp_t mem_flags)  {
    any(int, success);
    if (!(success == 0)) {
        return -1;
    } /*SYNTAX*/ 

    model__add_urb_record(urb, SENT);
    return 0; /*SYNTAX*/
} /*SYNTAX*/ 
void usb_kill_urb(struct urb *urb) {
    struct urb_hist_rec *rec = model__urb_get_record(urb);
    if (rec)
        rec->status = DONE;
} /*SYNTAX*/ 

// -- registering devices -- //
int input_register_device(struct input_dev *dev) {
    any(int, success);
    if (!(success == 0)) {
        return -1;
    } /*SYNTAX*/ 
    registered_dev = dev;
    return success;
} /*SYNTAX*/ 
void input_unregister_device(struct input_dev *dev) {
    assert(registered_dev == dev);
    registered_dev = NULL;
} /*SYNTAX*/ 

// -- pipes -- //
int usb_rcvintpipe(struct usb_device *dev, __u8 endpoint) {
    any(__u16, usb_maxpacket_ret);
    return usb_maxpacket_ret;
} /*SYNTAX*/ 
__u16 usb_maxpacket(struct usb_device *udev, int pipe, int is_out) {
    any(__u16, usb_maxpacket_ret);
    return usb_maxpacket_ret;
} /*SYNTAX*/ 