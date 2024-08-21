#include "spec_helpers.h"

// we define these inputs as globals so we can state invariants on them.
struct input_dev *dev;
struct urb *urb;
struct usb_interface * intf;


// captures same conditions as the combination of
// [<1] input_dev_reportable and the part of userdef_input_drvdata
// that is not dependent on is_open.
/*GLOBAL*/ bool inv__input_dev() {
/*GLOBAL*/     if (!names_obj(dev, struct input_dev))
/*GLOBAL*/         return false;
    
/*GLOBAL*/     struct usb_mouse *mouse = dev->dev.driver_data;
    
/*GLOBAL*/     return names_obj(mouse, struct usb_mouse) &&
/*GLOBAL*/            names_obj(mouse->irq, struct urb);
/*GLOBAL*/ } /*SYNTAX*/

/*GLOBAL*/ bool inv__urb() {
/*GLOBAL*/     if (!names_obj(urb, struct urb))
/*GLOBAL*/         return false;
    
    // complete_t_pred_fam gives this:
/*GLOBAL*/     assume(names_obj(urb->context, struct usb_mouse));
/*GLOBAL*/     struct usb_mouse *mouse = urb->context;
/*GLOBAL*/     void *buffer = mouse->data;

/*GLOBAL*/     return dev_reportable(mouse->dev) && 
/*GLOBAL*/            (!buffer || names_obj(buffer, char[8]));
/*GLOBAL*/ } /*SYNTAX*/

/*GLOBAL*/ bool inv__intf() {
/*GLOBAL*/     return names_obj(intf, struct usb_interface) &&
/*GLOBAL*/         names_obj(intf->cur_altsetting, struct usb_host_interface) &&
/*GLOBAL*/         names_obj(intf->cur_altsetting->endpoint, struct usb_host_endpoint) &&
/*GLOBAL*/         names_obj(intf->dev.parent, struct usb_device);
/*GLOBAL*/ } /*SYNTAX*/


// -- specs -- //

/*
 * My reading of the verifast predicates, (combined with https://www.oreilly.com/library/view/linux-device-drivers/0596005903/ch13.html)
 *  - urb_submitted(...) means that a request has been sent. We know the USB core received it. We don't own the URB anymore
 *  - complete_t_pred_fam(...) means the core processed the request and called the callback.
 *  - complete_t_pred_fam_out(...) means the callback is done with the request. We own the URB.
 */

/*SPECS*/ void spec__usb_mouse_open() {
/*SPECS*/     int res = usb_mouse_open(dev);
/*SPECS*/     if (res == 0) {
/*SPECS*/         assert(dev_is_opened(dev));
/*SPECS*/     } /*SYNTAX*/
/*SPECS*/ } /*SYNTAX*/

/*SPECS*/ void spec__usb_mouse_irq() {
    /*SPECS*/ assume(((struct usb_mouse*)urb->context)->data != NULL);
    /*SPECS*/ usb_mouse_irq(urb);
/*SPECS*/ } /*SYNTAX*/

/*SPECS*/ void spec__usb_mouse_close() {
/*SPECS*/     assume(dev_is_opened(dev));

/*SPECS*/     usb_mouse_close(dev);
    
/*SPECS*/     assert(dev_is_closed(dev));
/*SPECS*/ } /*SYNTAX*/

/*SPECS*/ void spec__usb_mouse_probe() {
/*SPECS*/     any(struct usb_device_id *, id);

/*SPECS*/     int res = usb_mouse_probe(intf, id);
/*SPECS*/     if (res == 0) {
/*SPECS*/         assert(dev_initialized(&intf->dev));
/*SPECS*/     } /*SYNTAX*/
/*SPECS*/ } /*SYNTAX*/

/*SPECS*/ void spec__usb_mouse_disconnect() {
/*SPECS*/     assume(dev_initialized(&intf->dev));

    // It is the input subsystem's responsibility to refcnt and potentially
    // free the input_dev struct once it's deregistered, not the driver's.
/*SPECS*/     struct input_dev *d = ((struct usb_mouse *)intf->dev.driver_data)->dev;

/*SPECS*/     usb_mouse_disconnect(intf);

    // must be deregistered but not freed by _disconnect.
/*SPECS*/     assert(names_obj(d, struct input_dev));
/*SPECS*/     assert(!dev_registered(d));
/*SPECS*/ } /*SYNTAX*/